-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1495_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:50:28.13401+00:00
-- url     : https://prove2.me/submissions/1a11a633-80dc-4d77-bcf9-db0cf10fea47

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
theorem support_rectangle_w1495_s6_0 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-37868561/200000000 : ℝ)*x 0 + (1358863429/2500000000 : ℝ)*x 1 + (5216729847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (37868561/200000000 : ℝ)^4487 ≤ (2315064917179/20000000000000 : ℝ)^3463 := by
    have hnat : (37868561 : ℕ)^4487*20000000000000^3463 ≤ 2315064917179^3463*200000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37868561 200000000 2315064917179 20000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358863429/2500000000 : ℝ)^4487 ≤ (2269424445937/5000000000000 : ℝ)^3463 := by
    have hnat : (1358863429 : ℕ)^4487*5000000000000^3463 ≤ 2269424445937^3463*2500000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358863429 2500000000 2269424445937 5000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216729847/10000000000 : ℝ)^4487 ≤ (4303618649071/10000000000000 : ℝ)^3463 := by
    have hnat : (5216729847 : ℕ)^4487*10000000000000^3463 ≤ 4303618649071^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216729847 10000000000 4303618649071 10000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-37868561/200000000 : ℝ), (1358863429/2500000000 : ℝ), (5216729847/10000000000 : ℝ)] ![(2315064917179/20000000000000 : ℝ), (2269424445937/5000000000000 : ℝ), (4303618649071/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-37868561/200000000 : ℝ)|^4487 ≤ (2315064917179/20000000000000 : ℝ)^3463
        have hw : |(-37868561/200000000 : ℝ)|=(37868561/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1358863429/2500000000 : ℝ)|^4487 ≤ (2269424445937/5000000000000 : ℝ)^3463
        have hw : |(1358863429/2500000000 : ℝ)|=(1358863429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216729847/10000000000 : ℝ)|^4487 ≤ (4303618649071/10000000000000 : ℝ)^3463
        have hw : |(5216729847/10000000000 : ℝ)|=(5216729847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_s6_1 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334532413/625000000 : ℝ)*x 0 + (-1002743559/5000000000 : ℝ)*x 1 + (5216729853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334532413/625000000 : ℝ)^4487 ≤ (5561648883427/12500000000000 : ℝ)^3463 := by
    have hnat : (334532413 : ℕ)^4487*12500000000000^3463 ≤ 5561648883427^3463*625000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334532413 625000000 5561648883427 12500000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1002743559/5000000000 : ℝ)^4487 ≤ (249412447131/2000000000000 : ℝ)^3463 := by
    have hnat : (1002743559 : ℕ)^4487*2000000000000^3463 ≤ 249412447131^3463*5000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002743559 5000000000 249412447131 2000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216729853/10000000000 : ℝ)^4487 ≤ (8607237310969/20000000000000 : ℝ)^3463 := by
    have hnat : (5216729853 : ℕ)^4487*20000000000000^3463 ≤ 8607237310969^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216729853 10000000000 8607237310969 20000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334532413/625000000 : ℝ), (-1002743559/5000000000 : ℝ), (5216729853/10000000000 : ℝ)] ![(5561648883427/12500000000000 : ℝ), (249412447131/2000000000000 : ℝ), (8607237310969/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334532413/625000000 : ℝ)|^4487 ≤ (5561648883427/12500000000000 : ℝ)^3463
        have hw : |(334532413/625000000 : ℝ)|=(334532413/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1002743559/5000000000 : ℝ)|^4487 ≤ (249412447131/2000000000000 : ℝ)^3463
        have hw : |(-1002743559/5000000000 : ℝ)|=(1002743559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216729853/10000000000 : ℝ)|^4487 ≤ (8607237310969/20000000000000 : ℝ)^3463
        have hw : |(5216729853/10000000000 : ℝ)|=(5216729853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_s6_2 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352518593/10000000000 : ℝ)*x 0 + (1043345973/2000000000 : ℝ)*x 1 + (-2005487123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352518593/10000000000 : ℝ)^4487 ≤ (22246595452929/50000000000000 : ℝ)^3463 := by
    have hnat : (5352518593 : ℕ)^4487*50000000000000^3463 ≤ 22246595452929^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352518593 10000000000 22246595452929 50000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043345973/2000000000 : ℝ)^4487 ≤ (43036186683113/100000000000000 : ℝ)^3463 := by
    have hnat : (1043345973 : ℕ)^4487*100000000000000^3463 ≤ 43036186683113^3463*2000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043345973 2000000000 43036186683113 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2005487123/10000000000 : ℝ)^4487 ≤ (2494124479367/20000000000000 : ℝ)^3463 := by
    have hnat : (2005487123 : ℕ)^4487*20000000000000^3463 ≤ 2494124479367^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005487123 10000000000 2494124479367 20000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352518593/10000000000 : ℝ), (1043345973/2000000000 : ℝ), (-2005487123/10000000000 : ℝ)] ![(22246595452929/50000000000000 : ℝ), (43036186683113/100000000000000 : ℝ), (2494124479367/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352518593/10000000000 : ℝ)|^4487 ≤ (22246595452929/50000000000000 : ℝ)^3463
        have hw : |(5352518593/10000000000 : ℝ)|=(5352518593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043345973/2000000000 : ℝ)|^4487 ≤ (43036186683113/100000000000000 : ℝ)^3463
        have hw : |(1043345973/2000000000 : ℝ)|=(1043345973/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2005487123/10000000000 : ℝ)|^4487 ≤ (2494124479367/20000000000000 : ℝ)^3463
        have hw : |(-2005487123/10000000000 : ℝ)|=(2005487123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_s6_3 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213887759/500000000 : ℝ)*x 0 + (201938911/500000000 : ℝ)*x 1 + (1132204437/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213887759/500000000 : ℝ)^4487 ≤ (16639391821601/50000000000000 : ℝ)^3463 := by
    have hnat : (213887759 : ℕ)^4487*50000000000000^3463 ≤ 16639391821601^3463*500000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213887759 500000000 16639391821601 50000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (201938911/500000000 : ℝ)^4487 ≤ (15445044760117/50000000000000 : ℝ)^3463 := by
    have hnat : (201938911 : ℕ)^4487*50000000000000^3463 ≤ 15445044760117^3463*500000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201938911 500000000 15445044760117 50000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1132204437/2500000000 : ℝ)^4487 ≤ (35831126824139/100000000000000 : ℝ)^3463 := by
    have hnat : (1132204437 : ℕ)^4487*100000000000000^3463 ≤ 35831126824139^3463*2500000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132204437 2500000000 35831126824139 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213887759/500000000 : ℝ), (201938911/500000000 : ℝ), (1132204437/2500000000 : ℝ)] ![(16639391821601/50000000000000 : ℝ), (15445044760117/50000000000000 : ℝ), (35831126824139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213887759/500000000 : ℝ)|^4487 ≤ (16639391821601/50000000000000 : ℝ)^3463
        have hw : |(213887759/500000000 : ℝ)|=(213887759/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(201938911/500000000 : ℝ)|^4487 ≤ (15445044760117/50000000000000 : ℝ)^3463
        have hw : |(201938911/500000000 : ℝ)|=(201938911/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1132204437/2500000000 : ℝ)|^4487 ≤ (35831126824139/100000000000000 : ℝ)^3463
        have hw : |(1132204437/2500000000 : ℝ)|=(1132204437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_s6_4 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1893458013/10000000000 : ℝ)*x 0 + (40764469/78125000 : ℝ)*x 1 + (5434323071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1893458013/10000000000 : ℝ)^4487 ≤ (1157556192771/10000000000000 : ℝ)^3463 := by
    have hnat : (1893458013 : ℕ)^4487*10000000000000^3463 ≤ 1157556192771^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1893458013 10000000000 1157556192771 10000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40764469/78125000 : ℝ)^4487 ≤ (21524090980543/50000000000000 : ℝ)^3463 := by
    have hnat : (40764469 : ℕ)^4487*50000000000000^3463 ≤ 21524090980543^3463*78125000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40764469 78125000 21524090980543 50000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5434323071/10000000000 : ℝ)^4487 ≤ (11344064025923/25000000000000 : ℝ)^3463 := by
    have hnat : (5434323071 : ℕ)^4487*25000000000000^3463 ≤ 11344064025923^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434323071 10000000000 11344064025923 25000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1893458013/10000000000 : ℝ), (40764469/78125000 : ℝ), (5434323071/10000000000 : ℝ)] ![(1157556192771/10000000000000 : ℝ), (21524090980543/50000000000000 : ℝ), (11344064025923/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1893458013/10000000000 : ℝ)|^4487 ≤ (1157556192771/10000000000000 : ℝ)^3463
        have hw : |(-1893458013/10000000000 : ℝ)|=(1893458013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(40764469/78125000 : ℝ)|^4487 ≤ (21524090980543/50000000000000 : ℝ)^3463
        have hw : |(40764469/78125000 : ℝ)|=(40764469/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5434323071/10000000000 : ℝ)|^4487 ≤ (11344064025923/25000000000000 : ℝ)^3463
        have hw : |(5434323071/10000000000 : ℝ)|=(5434323071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_s6_5 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529525317/1000000000 : ℝ)*x 0 + (-1787893693/10000000000 : ℝ)*x 1 + (5434323411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529525317/1000000000 : ℝ)^4487 ≤ (8775477475721/20000000000000 : ℝ)^3463 := by
    have hnat : (529525317 : ℕ)^4487*20000000000000^3463 ≤ 8775477475721^3463*1000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529525317 1000000000 8775477475721 20000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1787893693/10000000000 : ℝ)^4487 ≤ (5373176415193/50000000000000 : ℝ)^3463 := by
    have hnat : (1787893693 : ℕ)^4487*50000000000000^3463 ≤ 5373176415193^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1787893693 10000000000 5373176415193 50000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5434323411/10000000000 : ℝ)^4487 ≤ (45376259782149/100000000000000 : ℝ)^3463 := by
    have hnat : (5434323411 : ℕ)^4487*100000000000000^3463 ≤ 45376259782149^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434323411 10000000000 45376259782149 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529525317/1000000000 : ℝ), (-1787893693/10000000000 : ℝ), (5434323411/10000000000 : ℝ)] ![(8775477475721/20000000000000 : ℝ), (5373176415193/50000000000000 : ℝ), (45376259782149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529525317/1000000000 : ℝ)|^4487 ≤ (8775477475721/20000000000000 : ℝ)^3463
        have hw : |(529525317/1000000000 : ℝ)|=(529525317/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1787893693/10000000000 : ℝ)|^4487 ≤ (5373176415193/50000000000000 : ℝ)^3463
        have hw : |(-1787893693/10000000000 : ℝ)|=(1787893693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5434323411/10000000000 : ℝ)|^4487 ≤ (45376259782149/100000000000000 : ℝ)^3463
        have hw : |(5434323411/10000000000 : ℝ)|=(5434323411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_s6_6 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323813337/2500000000 : ℝ)*x 0 + (1358580841/2500000000 : ℝ)*x 1 + (-1787893511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323813337/2500000000 : ℝ)^4487 ≤ (43877389289679/100000000000000 : ℝ)^3463 := by
    have hnat : (1323813337 : ℕ)^4487*100000000000000^3463 ≤ 43877389289679^3463*2500000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323813337 2500000000 43877389289679 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358580841/2500000000 : ℝ)^4487 ≤ (5672032409207/12500000000000 : ℝ)^3463 := by
    have hnat : (1358580841 : ℕ)^4487*12500000000000^3463 ≤ 5672032409207^3463*2500000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358580841 2500000000 5672032409207 12500000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1787893511/10000000000 : ℝ)^4487 ≤ (537317570649/5000000000000 : ℝ)^3463 := by
    have hnat : (1787893511 : ℕ)^4487*5000000000000^3463 ≤ 537317570649^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1787893511 10000000000 537317570649 5000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323813337/2500000000 : ℝ), (1358580841/2500000000 : ℝ), (-1787893511/10000000000 : ℝ)] ![(43877389289679/100000000000000 : ℝ), (5672032409207/12500000000000 : ℝ), (537317570649/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323813337/2500000000 : ℝ)|^4487 ≤ (43877389289679/100000000000000 : ℝ)^3463
        have hw : |(1323813337/2500000000 : ℝ)|=(1323813337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1358580841/2500000000 : ℝ)|^4487 ≤ (5672032409207/12500000000000 : ℝ)^3463
        have hw : |(1358580841/2500000000 : ℝ)|=(1358580841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1787893511/10000000000 : ℝ)|^4487 ≤ (537317570649/5000000000000 : ℝ)^3463
        have hw : |(-1787893511/10000000000 : ℝ)|=(1787893511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_s6_7 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (171112883/400000000 : ℝ)*x 0 + (2263151709/5000000000 : ℝ)*x 1 + (4041310659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (171112883/400000000 : ℝ)^4487 ≤ (33279457937921/100000000000000 : ℝ)^3463 := by
    have hnat : (171112883 : ℕ)^4487*100000000000000^3463 ≤ 33279457937921^3463*400000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171112883 400000000 33279457937921 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2263151709/5000000000 : ℝ)^4487 ≤ (7161070754747/20000000000000 : ℝ)^3463 := by
    have hnat : (2263151709 : ℕ)^4487*20000000000000^3463 ≤ 7161070754747^3463*5000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2263151709 5000000000 7161070754747 20000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4041310659/10000000000 : ℝ)^4487 ≤ (15457594132039/50000000000000 : ℝ)^3463 := by
    have hnat : (4041310659 : ℕ)^4487*50000000000000^3463 ≤ 15457594132039^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4041310659 10000000000 15457594132039 50000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(171112883/400000000 : ℝ), (2263151709/5000000000 : ℝ), (4041310659/10000000000 : ℝ)] ![(33279457937921/100000000000000 : ℝ), (7161070754747/20000000000000 : ℝ), (15457594132039/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(171112883/400000000 : ℝ)|^4487 ≤ (33279457937921/100000000000000 : ℝ)^3463
        have hw : |(171112883/400000000 : ℝ)|=(171112883/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2263151709/5000000000 : ℝ)|^4487 ≤ (7161070754747/20000000000000 : ℝ)^3463
        have hw : |(2263151709/5000000000 : ℝ)|=(2263151709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4041310659/10000000000 : ℝ)|^4487 ≤ (15457594132039/50000000000000 : ℝ)^3463
        have hw : |(4041310659/10000000000 : ℝ)|=(4041310659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1495_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40505603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (387/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10847/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (339/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15479/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (387/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10847/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (387/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10847/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (387/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10847/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (387/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10847/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (387/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10847/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (387/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10847/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10847/100000 : ℝ) ^ (4485/1024 : ℝ) ≤ (595345771750073/10000000000000000000 : ℝ) := by
    have hpowers : (10847/100000 : ℝ)^4485 ≤ (595345771750073/10000000000000000000 : ℝ)^1024 := by
      have hnat : (10847 : ℕ)^4485*10000000000000000000^1024 ≤ 595345771750073^1024*100000^4485 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10847 100000 595345771750073 10000000000000000000 4485 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10847/100000 : ℝ)) (X := (595345771750073/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4485 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (387/2500 : ℝ) ^ (4485/1024 : ℝ) ≤ (141338911341279/500000000000000000 : ℝ) := by
    have hpowers : (387/2500 : ℝ)^4485 ≤ (141338911341279/500000000000000000 : ℝ)^1024 := by
      have hnat : (387 : ℕ)^4485*500000000000000000^1024 ≤ 141338911341279^1024*2500^4485 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        387 2500 141338911341279 500000000000000000 4485 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (387/2500 : ℝ)) (X := (141338911341279/500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4485 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000595345771750073/5000000000000000000 : ℝ) ≤ (2500067960542311/2500000000000000 : ℝ) ^ (4485/1024 : ℝ) := by
    have hpowers : (5000595345771750073/5000000000000000000 : ℝ)^1024 ≤ (2500067960542311/2500000000000000 : ℝ)^4485 := by
      have hnat : (5000595345771750073 : ℕ)^1024*2500000000000000^4485 ≤ 2500067960542311^4485*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000595345771750073 5000000000000000000 2500067960542311 2500000000000000 1024 4485 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500067960542311/2500000000000000 : ℝ)) (X := (5000595345771750073/5000000000000000000 : ℝ)) (by norm_num) 4485 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10003422123998575653/10000000000000000000 : ℝ) ≤ (2500195306151999/2500000000000000 : ℝ) ^ (4485/1024 : ℝ) := by
    have hpowers : (10003422123998575653/10000000000000000000 : ℝ)^1024 ≤ (2500195306151999/2500000000000000 : ℝ)^4485 := by
      have hnat : (10003422123998575653 : ℕ)^1024*2500000000000000^4485 ≤ 2500195306151999^4485*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003422123998575653 10000000000000000000 2500195306151999 2500000000000000 1024 4485 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500195306151999/2500000000000000 : ℝ)) (X := (10003422123998575653/10000000000000000000 : ℝ)) (by norm_num) 4485 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (250141338911341279/250000000000000000 : ℝ) ≤ (2500322651761687/2500000000000000 : ℝ) ^ (4485/1024 : ℝ) := by
    have hpowers : (250141338911341279/250000000000000000 : ℝ)^1024 ≤ (2500322651761687/2500000000000000 : ℝ)^4485 := by
      have hnat : (250141338911341279 : ℕ)^1024*2500000000000000^4485 ≤ 2500322651761687^4485*250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        250141338911341279 250000000000000000 2500322651761687 2500000000000000 1024 4485 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500322651761687/2500000000000000 : ℝ)) (X := (250141338911341279/250000000000000000 : ℝ)) (by norm_num) 4485 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(595345771750073/10000000000000000000 : ℝ) ≤ ((11580052225535955391/11582500000000000000 : ℝ)+2*(15918201211/14478125000000 : ℝ)*(10847/100000 : ℝ))^(4485/1024 : ℝ) := by
    rw [show (11580052225535955391/11582500000000000000 : ℝ)+2*(15918201211/14478125000000 : ℝ)*(10847/100000 : ℝ)=(2500067960542311/2500000000000000 : ℝ) by norm_num, show 1+2*(595345771750073/10000000000000000000 : ℝ)=(5000595345771750073/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(141338911341279/500000000000000000 : ℝ)+(595345771750073/10000000000000000000 : ℝ) ≤ ((11580052225535955391/11582500000000000000 : ℝ)+(15918201211/14478125000000 : ℝ)*((387/2500 : ℝ)+(10847/100000 : ℝ)))^(4485/1024 : ℝ) := by
    rw [show (11580052225535955391/11582500000000000000 : ℝ)+(15918201211/14478125000000 : ℝ)*((387/2500 : ℝ)+(10847/100000 : ℝ))=(2500195306151999/2500000000000000 : ℝ) by norm_num, show 1+(141338911341279/500000000000000000 : ℝ)+(595345771750073/10000000000000000000 : ℝ)=(10003422123998575653/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(141338911341279/500000000000000000 : ℝ) ≤ ((11580052225535955391/11582500000000000000 : ℝ)+2*(15918201211/14478125000000 : ℝ)*(387/2500 : ℝ))^(4485/1024 : ℝ) := by
    rw [show (11580052225535955391/11582500000000000000 : ℝ)+2*(15918201211/14478125000000 : ℝ)*(387/2500 : ℝ)=(2500322651761687/2500000000000000 : ℝ) by norm_num, show 1+2*(141338911341279/500000000000000000 : ℝ)=(250141338911341279/250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11580052225535955391/11582500000000000000 : ℝ)*(X 1 0+X 2 0)+(15918201211/14478125000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4485/1024 : ℝ)) (lo := (10847/100000 : ℝ)) (hi := (387/2500 : ℝ)) (c := (11580052225535955391/11582500000000000000 : ℝ)) (alpha := (15918201211/14478125000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11580052225535955391/11582500000000000000 : ℝ)*(X 0 1+X 2 1)+(15918201211/14478125000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4485/1024 : ℝ)) (lo := (10847/100000 : ℝ)) (hi := (387/2500 : ℝ)) (c := (11580052225535955391/11582500000000000000 : ℝ)) (alpha := (15918201211/14478125000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11580052225535955391/11582500000000000000 : ℝ)*(X 0 2+X 1 2)+(15918201211/14478125000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4485/1024 : ℝ)) (lo := (10847/100000 : ℝ)) (hi := (387/2500 : ℝ)) (c := (11580052225535955391/11582500000000000000 : ℝ)) (alpha := (15918201211/14478125000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-37868561/200000000 : ℝ)*X 0 0+(1358863429/2500000000 : ℝ)*X 0 1+(5216729847/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334532413/625000000 : ℝ)*X 1 0+(-1002743559/5000000000 : ℝ)*X 1 1+(5216729853/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352518593/10000000000 : ℝ)*X 2 0+(1043345973/2000000000 : ℝ)*X 2 1+(-2005487123/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((213887759/500000000 : ℝ)*X 0 0+(201938911/500000000 : ℝ)*X 0 1+(1132204437/2500000000 : ℝ)*X 0 2+(213887759/500000000 : ℝ)*X 1 0+(201938911/500000000 : ℝ)*X 1 1+(1132204437/2500000000 : ℝ)*X 1 2+(213887759/500000000 : ℝ)*X 2 0+(201938911/500000000 : ℝ)*X 2 1+(1132204437/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1893458013/10000000000 : ℝ)*X 0 0+(40764469/78125000 : ℝ)*X 0 1+(5434323071/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((529525317/1000000000 : ℝ)*X 1 0+(-1787893693/10000000000 : ℝ)*X 1 1+(5434323411/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1323813337/2500000000 : ℝ)*X 2 0+(1358580841/2500000000 : ℝ)*X 2 1+(-1787893511/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((171112883/400000000 : ℝ)*X 0 0+(2263151709/5000000000 : ℝ)*X 0 1+(4041310659/10000000000 : ℝ)*X 0 2+(171112883/400000000 : ℝ)*X 1 0+(2263151709/5000000000 : ℝ)*X 1 1+(4041310659/10000000000 : ℝ)*X 1 2+(171112883/400000000 : ℝ)*X 2 0+(2263151709/5000000000 : ℝ)*X 2 1+(4041310659/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (54344697185086678231929/4633000000000000000000000000 : ℝ) := by norm_num
    linear_combination (103008307/5000000000000 : ℝ)*(base19) + (950262707/50000000000000 : ℝ)*(base23) + (78589937/100000000000000 : ℝ)*(lower2) + (73641003/25000000000000 : ℝ)*(upper3) + (90105519/50000000000000 : ℝ)*(upper5) + (661272169003603/20000000000000 : ℝ)*(major0) + (661272169003603/20000000000000 : ℝ)*(major1) + (661272169003603/20000000000000 : ℝ)*(major2) + (4572008257321967/100000000000000 : ℝ)*(sp0) + (457203807371513/10000000000000 : ℝ)*(sp1) + (285752389584741/6250000000000 : ℝ)*(sp2) + (510166384884281/25000000000000 : ℝ)*(sp3) + (31876559303/100000000000000 : ℝ)*(sp4) + (1953202557/12500000000000 : ℝ)*(sp7) + (102034058257879/5000000000000 : ℝ)*(f.failure) + (457204013388127/10000000000000 : ℝ)*(f.sum) + (2595875936233/4633000000000000000000000000 : ℝ)*base65 + (1002097879755273773/231650000000000000000000000000000 : ℝ)*base67 + (38903599027026227/231650000000000000000000000000000 : ℝ)*base70 + (1361591668438673773/231650000000000000000000000000000 : ℝ)*base71 + (6453203790357/1158250000000000000000000000 : ℝ)*base74 + (1743511087558226227/231650000000000000000000000000000 : ℝ)*base76 + (1652010723288526227/231650000000000000000000000000000 : ℝ)*base78 + (3063271773681473773/231650000000000000000000000000000 : ℝ)*base79 + (2058948962089/579125000000000000000000000 : ℝ)*base81 + (353963/125000000000000000000 : ℝ)*base90 + (353963/125000000000000000000 : ℝ)*base92 + (353963/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (162998476461299305036647/23165000000000000000000000000 : ℝ) := by norm_num
    linear_combination (186965931/12500000000000 : ℝ)*(base19) + (1727334659/100000000000000 : ℝ)*(base23) + (537296851/100000000000000 : ℝ)*(lower1) + (302667901/100000000000000 : ℝ)*(upper3) + (438521/100000000000000 : ℝ)*(lower4) + (47766319/25000000000000 : ℝ)*(upper5) + (417587882698371/12500000000000 : ℝ)*(major0) + (417587882698371/12500000000000 : ℝ)*(major1) + (417587882698371/12500000000000 : ℝ)*(major2) + (6980810193/100000000000000 : ℝ)*(sp2) + (577441094590383/12500000000000 : ℝ)*(sp4) + (144360226906113/3125000000000 : ℝ)*(sp5) + (1154880012144553/25000000000000 : ℝ)*(sp6) + (1030938565951903/50000000000000 : ℝ)*(sp7) + (1030938565951903/50000000000000 : ℝ)*(f.failure) + (577441094590383/12500000000000 : ℝ)*(f.sum) + (1996851121483/11582500000000000000000000000 : ℝ)*base65 + (3874112274084206939/144781250000000000000000000000000 : ℝ)*base68 + (1434509032050605561/144781250000000000000000000000000 : ℝ)*base69 + (615200267276355561/144781250000000000000000000000000 : ℝ)*base71 + (12132384828591/5791250000000000000000000000 : ℝ)*base74 + (5825424645326144439/144781250000000000000000000000000 : ℝ)*base76 + (686262930119425689/144781250000000000000000000000000 : ℝ)*base78 + (1190510592473761811/144781250000000000000000000000000 : ℝ)*base79 + (118882014696241/23165000000000000000000000000 : ℝ)*base81 + (12509/1250000000000000000000 : ℝ)*base89 + (12509/1250000000000000000000 : ℝ)*base91 + (12509/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1495_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40505603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (387/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10847/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (339/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1495_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1495_s7_0 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-946714433/5000000000 : ℝ)*x 0 + (5435447419/10000000000 : ℝ)*x 1 + (1043347123/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (946714433/5000000000 : ℝ)^4487 ≤ (231506620991/2000000000000 : ℝ)^3463 := by
    have hnat : (946714433 : ℕ)^4487*2000000000000^3463 ≤ 231506620991^3463*5000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      946714433 5000000000 231506620991 2000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435447419/10000000000 : ℝ)^4487 ≤ (4538842078737/10000000000000 : ℝ)^3463 := by
    have hnat : (5435447419 : ℕ)^4487*10000000000000^3463 ≤ 4538842078737^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435447419 10000000000 4538842078737 10000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043347123/2000000000 : ℝ)^4487 ≤ (43036248145147/100000000000000 : ℝ)^3463 := by
    have hnat : (1043347123 : ℕ)^4487*100000000000000^3463 ≤ 43036248145147^3463*2000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043347123 2000000000 43036248145147 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-946714433/5000000000 : ℝ), (5435447419/10000000000 : ℝ), (1043347123/2000000000 : ℝ)] ![(231506620991/2000000000000 : ℝ), (4538842078737/10000000000000 : ℝ), (43036248145147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-946714433/5000000000 : ℝ)|^4487 ≤ (231506620991/2000000000000 : ℝ)^3463
        have hw : |(-946714433/5000000000 : ℝ)|=(946714433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435447419/10000000000 : ℝ)|^4487 ≤ (4538842078737/10000000000000 : ℝ)^3463
        have hw : |(5435447419/10000000000 : ℝ)|=(5435447419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043347123/2000000000 : ℝ)|^4487 ≤ (43036248145147/100000000000000 : ℝ)^3463
        have hw : |(1043347123/2000000000 : ℝ)|=(1043347123/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_s7_1 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338129253/2500000000 : ℝ)*x 0 + (-2005481617/10000000000 : ℝ)*x 1 + (652091951/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338129253/2500000000 : ℝ)^4487 ≤ (44493173877577/100000000000000 : ℝ)^3463 := by
    have hnat : (1338129253 : ℕ)^4487*100000000000000^3463 ≤ 44493173877577^3463*2500000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338129253 2500000000 44493173877577 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2005481617/10000000000 : ℝ)^4487 ≤ (389705563599/3125000000000 : ℝ)^3463 := by
    have hnat : (2005481617 : ℕ)^4487*3125000000000^3463 ≤ 389705563599^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005481617 10000000000 389705563599 3125000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652091951/1250000000 : ℝ)^4487 ≤ (10759062017581/25000000000000 : ℝ)^3463 := by
    have hnat : (652091951 : ℕ)^4487*25000000000000^3463 ≤ 10759062017581^3463*1250000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652091951 1250000000 10759062017581 25000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338129253/2500000000 : ℝ), (-2005481617/10000000000 : ℝ), (652091951/1250000000 : ℝ)] ![(44493173877577/100000000000000 : ℝ), (389705563599/3125000000000 : ℝ), (10759062017581/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338129253/2500000000 : ℝ)|^4487 ≤ (44493173877577/100000000000000 : ℝ)^3463
        have hw : |(1338129253/2500000000 : ℝ)|=(1338129253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2005481617/10000000000 : ℝ)|^4487 ≤ (389705563599/3125000000000 : ℝ)^3463
        have hw : |(-2005481617/10000000000 : ℝ)|=(2005481617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(652091951/1250000000 : ℝ)|^4487 ≤ (10759062017581/25000000000000 : ℝ)^3463
        have hw : |(652091951/1250000000 : ℝ)|=(652091951/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_s7_2 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676258497/5000000000 : ℝ)*x 0 + (1304183911/2500000000 : ℝ)*x 1 + (-1002740797/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676258497/5000000000 : ℝ)^4487 ≤ (44493173683707/100000000000000 : ℝ)^3463 := by
    have hnat : (2676258497 : ℕ)^4487*100000000000000^3463 ≤ 44493173683707^3463*5000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676258497 5000000000 44493173683707 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304183911/2500000000 : ℝ)^4487 ≤ (4303624845513/10000000000000 : ℝ)^3463 := by
    have hnat : (1304183911 : ℕ)^4487*10000000000000^3463 ≤ 4303624845513^3463*2500000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304183911 2500000000 4303624845513 10000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1002740797/5000000000 : ℝ)^4487 ≤ (6235288924929/50000000000000 : ℝ)^3463 := by
    have hnat : (1002740797 : ℕ)^4487*50000000000000^3463 ≤ 6235288924929^3463*5000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002740797 5000000000 6235288924929 50000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676258497/5000000000 : ℝ), (1304183911/2500000000 : ℝ), (-1002740797/5000000000 : ℝ)] ![(44493173683707/100000000000000 : ℝ), (4303624845513/10000000000000 : ℝ), (6235288924929/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676258497/5000000000 : ℝ)|^4487 ≤ (44493173683707/100000000000000 : ℝ)^3463
        have hw : |(2676258497/5000000000 : ℝ)|=(2676258497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304183911/2500000000 : ℝ)|^4487 ≤ (4303624845513/10000000000000 : ℝ)^3463
        have hw : |(1304183911/2500000000 : ℝ)|=(1304183911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1002740797/5000000000 : ℝ)|^4487 ≤ (6235288924929/50000000000000 : ℝ)^3463
        have hw : |(-1002740797/5000000000 : ℝ)|=(1002740797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_s7_3 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267359737/625000000 : ℝ)*x 0 + (4038791677/10000000000 : ℝ)*x 1 + (4528804137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267359737/625000000 : ℝ)^4487 ≤ (6655757962417/20000000000000 : ℝ)^3463 := by
    have hnat : (267359737 : ℕ)^4487*20000000000000^3463 ≤ 6655757962417^3463*625000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267359737 625000000 6655757962417 20000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4038791677/10000000000 : ℝ)^4487 ≤ (30890222878889/100000000000000 : ℝ)^3463 := by
    have hnat : (4038791677 : ℕ)^4487*100000000000000^3463 ≤ 30890222878889^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4038791677 10000000000 30890222878889 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4528804137/10000000000 : ℝ)^4487 ≤ (17915493646837/50000000000000 : ℝ)^3463 := by
    have hnat : (4528804137 : ℕ)^4487*50000000000000^3463 ≤ 17915493646837^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4528804137 10000000000 17915493646837 50000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267359737/625000000 : ℝ), (4038791677/10000000000 : ℝ), (4528804137/10000000000 : ℝ)] ![(6655757962417/20000000000000 : ℝ), (30890222878889/100000000000000 : ℝ), (17915493646837/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267359737/625000000 : ℝ)|^4487 ≤ (6655757962417/20000000000000 : ℝ)^3463
        have hw : |(267359737/625000000 : ℝ)|=(267359737/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4038791677/10000000000 : ℝ)|^4487 ≤ (30890222878889/100000000000000 : ℝ)^3463
        have hw : |(4038791677/10000000000 : ℝ)|=(4038791677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4528804137/10000000000 : ℝ)|^4487 ≤ (17915493646837/50000000000000 : ℝ)^3463
        have hw : |(4528804137/10000000000 : ℝ)|=(4528804137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_s7_4 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-946729321/5000000000 : ℝ)*x 0 + (326116097/625000000 : ℝ)*x 1 + (1358579289/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (946729321/5000000000 : ℝ)^4487 ≤ (5787783455067/50000000000000 : ℝ)^3463 := by
    have hnat : (946729321 : ℕ)^4487*50000000000000^3463 ≤ 5787783455067^3463*5000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      946729321 5000000000 5787783455067 50000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (326116097/625000000 : ℝ)^4487 ≤ (43048240968391/100000000000000 : ℝ)^3463 := by
    have hnat : (326116097 : ℕ)^4487*100000000000000^3463 ≤ 43048240968391^3463*625000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326116097 625000000 43048240968391 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358579289/2500000000 : ℝ)^4487 ≤ (45376192109367/100000000000000 : ℝ)^3463 := by
    have hnat : (1358579289 : ℕ)^4487*100000000000000^3463 ≤ 45376192109367^3463*2500000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358579289 2500000000 45376192109367 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-946729321/5000000000 : ℝ), (326116097/625000000 : ℝ), (1358579289/2500000000 : ℝ)] ![(5787783455067/50000000000000 : ℝ), (43048240968391/100000000000000 : ℝ), (45376192109367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-946729321/5000000000 : ℝ)|^4487 ≤ (5787783455067/50000000000000 : ℝ)^3463
        have hw : |(-946729321/5000000000 : ℝ)|=(946729321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(326116097/625000000 : ℝ)|^4487 ≤ (43048240968391/100000000000000 : ℝ)^3463
        have hw : |(326116097/625000000 : ℝ)|=(326116097/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358579289/2500000000 : ℝ)|^4487 ≤ (45376192109367/100000000000000 : ℝ)^3463
        have hw : |(1358579289/2500000000 : ℝ)|=(1358579289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_s7_5 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534727791/1250000000 : ℝ)*x 0 + (181051613/400000000 : ℝ)*x 1 + (2020661971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534727791/1250000000 : ℝ)^4487 ≤ (33279460488141/100000000000000 : ℝ)^3463 := by
    have hnat : (534727791 : ℕ)^4487*100000000000000^3463 ≤ 33279460488141^3463*1250000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534727791 1250000000 33279460488141 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (181051613/400000000 : ℝ)^4487 ≤ (35805219575481/100000000000000 : ℝ)^3463 := by
    have hnat : (181051613 : ℕ)^4487*100000000000000^3463 ≤ 35805219575481^3463*400000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181051613 400000000 35805219575481 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2020661971/5000000000 : ℝ)^4487 ≤ (7728829980699/25000000000000 : ℝ)^3463 := by
    have hnat : (2020661971 : ℕ)^4487*25000000000000^3463 ≤ 7728829980699^3463*5000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2020661971 5000000000 7728829980699 25000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534727791/1250000000 : ℝ), (181051613/400000000 : ℝ), (2020661971/5000000000 : ℝ)] ![(33279460488141/100000000000000 : ℝ), (35805219575481/100000000000000 : ℝ), (7728829980699/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534727791/1250000000 : ℝ)|^4487 ≤ (33279460488141/100000000000000 : ℝ)^3463
        have hw : |(534727791/1250000000 : ℝ)|=(534727791/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(181051613/400000000 : ℝ)|^4487 ≤ (35805219575481/100000000000000 : ℝ)^3463
        have hw : |(181051613/400000000 : ℝ)|=(181051613/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2020661971/5000000000 : ℝ)|^4487 ≤ (7728829980699/25000000000000 : ℝ)^3463
        have hw : |(2020661971/5000000000 : ℝ)|=(2020661971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1495_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40505603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (339/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (10849/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15479/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15479/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (339/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15479/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (339/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15479/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (339/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15479/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (339/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15479/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (339/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15479/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (339/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (339/3125 : ℝ) ^ (4485/1024 : ℝ) ≤ (5955862023754317/100000000000000000000 : ℝ) := by
    have hpowers : (339/3125 : ℝ)^4485 ≤ (5955862023754317/100000000000000000000 : ℝ)^1024 := by
      have hnat : (339 : ℕ)^4485*100000000000000000000^1024 ≤ 5955862023754317^1024*3125^4485 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        339 3125 5955862023754317 100000000000000000000 4485 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (339/3125 : ℝ)) (X := (5955862023754317/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4485 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15479/100000 : ℝ) ^ (4485/1024 : ℝ) ≤ (5651957021374839/20000000000000000000 : ℝ) := by
    have hpowers : (15479/100000 : ℝ)^4485 ≤ (5651957021374839/20000000000000000000 : ℝ)^1024 := by
      have hnat : (15479 : ℕ)^4485*20000000000000000000^1024 ≤ 5651957021374839^1024*100000^4485 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15479 100000 5651957021374839 20000000000000000000 4485 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15479/100000 : ℝ)) (X := (5651957021374839/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4485 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005955862023754317/50000000000000000000 : ℝ) ≤ (5000135975973883/5000000000000000 : ℝ) ^ (4485/1024 : ℝ) := by
    have hpowers : (50005955862023754317/50000000000000000000 : ℝ)^1024 ≤ (5000135975973883/5000000000000000 : ℝ)^4485 := by
      have hnat : (50005955862023754317 : ℕ)^1024*5000000000000000^4485 ≤ 5000135975973883^4485*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005955862023754317 50000000000000000000 5000135975973883 5000000000000000 1024 4485 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000135975973883/5000000000000000 : ℝ)) (X := (50005955862023754317/50000000000000000000 : ℝ)) (by norm_num) 4485 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126069238972832141/3125000000000000000 : ℝ) ≤ (2500195274236883/2500000000000000 : ℝ) ^ (4485/1024 : ℝ) := by
    have hpowers : (3126069238972832141/3125000000000000000 : ℝ)^1024 ≤ (2500195274236883/2500000000000000 : ℝ)^4485 := by
      have hnat : (3126069238972832141 : ℕ)^1024*2500000000000000^4485 ≤ 2500195274236883^4485*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126069238972832141 3125000000000000000 2500195274236883 2500000000000000 1024 4485 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500195274236883/2500000000000000 : ℝ)) (X := (3126069238972832141/3125000000000000000 : ℝ)) (by norm_num) 4485 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005651957021374839/10000000000000000000 : ℝ) ≤ (5000645120973649/5000000000000000 : ℝ) ^ (4485/1024 : ℝ) := by
    have hpowers : (10005651957021374839/10000000000000000000 : ℝ)^1024 ≤ (5000645120973649/5000000000000000 : ℝ)^4485 := by
      have hnat : (10005651957021374839 : ℕ)^1024*5000000000000000^4485 ≤ 5000645120973649^4485*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005651957021374839 10000000000000000000 5000645120973649 5000000000000000 1024 4485 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000645120973649/5000000000000000 : ℝ)) (X := (10005651957021374839/10000000000000000000 : ℝ)) (by norm_num) 4485 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5955862023754317/100000000000000000000 : ℝ) ≤ ((4630021299955518121/4631000000000000000 : ℝ)+2*(254572499883/231550000000000 : ℝ)*(339/3125 : ℝ))^(4485/1024 : ℝ) := by
    rw [show (4630021299955518121/4631000000000000000 : ℝ)+2*(254572499883/231550000000000 : ℝ)*(339/3125 : ℝ)=(5000135975973883/5000000000000000 : ℝ) by norm_num, show 1+2*(5955862023754317/100000000000000000000 : ℝ)=(50005955862023754317/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5651957021374839/20000000000000000000 : ℝ)+(5955862023754317/100000000000000000000 : ℝ) ≤ ((4630021299955518121/4631000000000000000 : ℝ)+(254572499883/231550000000000 : ℝ)*((15479/100000 : ℝ)+(339/3125 : ℝ)))^(4485/1024 : ℝ) := by
    rw [show (4630021299955518121/4631000000000000000 : ℝ)+(254572499883/231550000000000 : ℝ)*((15479/100000 : ℝ)+(339/3125 : ℝ))=(2500195274236883/2500000000000000 : ℝ) by norm_num, show 1+(5651957021374839/20000000000000000000 : ℝ)+(5955862023754317/100000000000000000000 : ℝ)=(3126069238972832141/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5651957021374839/20000000000000000000 : ℝ) ≤ ((4630021299955518121/4631000000000000000 : ℝ)+2*(254572499883/231550000000000 : ℝ)*(15479/100000 : ℝ))^(4485/1024 : ℝ) := by
    rw [show (4630021299955518121/4631000000000000000 : ℝ)+2*(254572499883/231550000000000 : ℝ)*(15479/100000 : ℝ)=(5000645120973649/5000000000000000 : ℝ) by norm_num, show 1+2*(5651957021374839/20000000000000000000 : ℝ)=(10005651957021374839/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4630021299955518121/4631000000000000000 : ℝ)*(X 1 0+X 2 0)+(254572499883/231550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4485/1024 : ℝ)) (lo := (339/3125 : ℝ)) (hi := (15479/100000 : ℝ)) (c := (4630021299955518121/4631000000000000000 : ℝ)) (alpha := (254572499883/231550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4630021299955518121/4631000000000000000 : ℝ)*(X 0 1+X 2 1)+(254572499883/231550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4485/1024 : ℝ)) (lo := (339/3125 : ℝ)) (hi := (15479/100000 : ℝ)) (c := (4630021299955518121/4631000000000000000 : ℝ)) (alpha := (254572499883/231550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4630021299955518121/4631000000000000000 : ℝ)*(X 0 2+X 1 2)+(254572499883/231550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4485/1024 : ℝ)) (lo := (339/3125 : ℝ)) (hi := (15479/100000 : ℝ)) (c := (4630021299955518121/4631000000000000000 : ℝ)) (alpha := (254572499883/231550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-946714433/5000000000 : ℝ)*X 0 0+(5435447419/10000000000 : ℝ)*X 0 1+(1043347123/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338129253/2500000000 : ℝ)*X 1 0+(-2005481617/10000000000 : ℝ)*X 1 1+(652091951/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676258497/5000000000 : ℝ)*X 2 0+(1304183911/2500000000 : ℝ)*X 2 1+(-1002740797/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((267359737/625000000 : ℝ)*X 0 0+(4038791677/10000000000 : ℝ)*X 0 1+(4528804137/10000000000 : ℝ)*X 0 2+(267359737/625000000 : ℝ)*X 1 0+(4038791677/10000000000 : ℝ)*X 1 1+(4528804137/10000000000 : ℝ)*X 1 2+(267359737/625000000 : ℝ)*X 2 0+(4038791677/10000000000 : ℝ)*X 2 1+(4528804137/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-946729321/5000000000 : ℝ)*X 0 0+(326116097/625000000 : ℝ)*X 0 1+(1358579289/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((534727791/1250000000 : ℝ)*X 0 0+(181051613/400000000 : ℝ)*X 0 1+(2020661971/5000000000 : ℝ)*X 0 2+(534727791/1250000000 : ℝ)*X 1 0+(181051613/400000000 : ℝ)*X 1 1+(2020661971/5000000000 : ℝ)*X 1 2+(534727791/1250000000 : ℝ)*X 2 0+(181051613/400000000 : ℝ)*X 2 1+(2020661971/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s7_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (132510300722416019225227467/46310000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (253299077/50000000000000 : ℝ)*(base19) + (444586539/100000000000000 : ℝ)*(base23) + (4992357/20000000000000 : ℝ)*(lower2) + (16105699/25000000000000 : ℝ)*(upper3) + (49735293/100000000000000 : ℝ)*(upper5) + (661301463593803/20000000000000 : ℝ)*(major0) + (661301463593803/20000000000000 : ℝ)*(major1) + (661301463593803/20000000000000 : ℝ)*(major2) + (4572234943519783/100000000000000 : ℝ)*(sp0) + (2286121232954049/50000000000000 : ℝ)*(sp1) + (4572242527919713/100000000000000 : ℝ)*(sp2) + (510191962753761/25000000000000 : ℝ)*(sp3) + (2007246617/25000000000000 : ℝ)*(sp4) + (3717037539/100000000000000 : ℝ)*(sp5) + (1020385784026291/50000000000000 : ℝ)*(f.failure) + (1143060743126563/25000000000000 : ℝ)*(f.sum) + (6815005155947/1157750000000000000000000000 : ℝ)*base66 + (1065277903674335837/92620000000000000000000000000000 : ℝ)*base68 + (834109214934995837/92620000000000000000000000000000 : ℝ)*base70 + (476545675687135837/92620000000000000000000000000000 : ℝ)*base72 + (34704220635509/4631000000000000000000000000 : ℝ)*base74 + (1493076158746215837/92620000000000000000000000000000 : ℝ)*base76 + (1284797768437655837/92620000000000000000000000000000 : ℝ)*base78 + (1040729320832915837/92620000000000000000000000000000 : ℝ)*base80 + (14255288251433/2315500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (2691527/1250000000000000000000 : ℝ)*base90 + (2691527/1250000000000000000000 : ℝ)*base92 + (2691527/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1495_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40505603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (339/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10849/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1495_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1495_box_0 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1676709591/10000000000 : ℝ)*x 0 + (675584231/1250000000 : ℝ)*x 1 + (5404672119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1676709591/10000000000 : ℝ)^4487 ≤ (9888537670779/100000000000000 : ℝ)^3463 := by
    have hnat : (1676709591 : ℕ)^4487*100000000000000^3463 ≤ 9888537670779^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1676709591 10000000000 9888537670779 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675584231/1250000000 : ℝ)^4487 ≤ (22527870246791/50000000000000 : ℝ)^3463 := by
    have hnat : (675584231 : ℕ)^4487*50000000000000^3463 ≤ 22527870246791^3463*1250000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675584231 1250000000 22527870246791 50000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5404672119/10000000000 : ℝ)^4487 ≤ (45055721817783/100000000000000 : ℝ)^3463 := by
    have hnat : (5404672119 : ℕ)^4487*100000000000000^3463 ≤ 45055721817783^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404672119 10000000000 45055721817783 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1676709591/10000000000 : ℝ), (675584231/1250000000 : ℝ), (5404672119/10000000000 : ℝ)] ![(9888537670779/100000000000000 : ℝ), (22527870246791/50000000000000 : ℝ), (45055721817783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1676709591/10000000000 : ℝ)|^4487 ≤ (9888537670779/100000000000000 : ℝ)^3463
        have hw : |(-1676709591/10000000000 : ℝ)|=(1676709591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(675584231/1250000000 : ℝ)|^4487 ≤ (22527870246791/50000000000000 : ℝ)^3463
        have hw : |(675584231/1250000000 : ℝ)|=(675584231/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5404672119/10000000000 : ℝ)|^4487 ≤ (45055721817783/100000000000000 : ℝ)^3463
        have hw : |(5404672119/10000000000 : ℝ)|=(5404672119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_box_1 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527052169/1000000000 : ℝ)*x 0 + (-232833009/1250000000 : ℝ)*x 1 + (5404672799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527052169/1000000000 : ℝ)^4487 ≤ (10903011132029/25000000000000 : ℝ)^3463 := by
    have hnat : (527052169 : ℕ)^4487*25000000000000^3463 ≤ 10903011132029^3463*1000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527052169 1000000000 10903011132029 25000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (232833009/1250000000 : ℝ)^4487 ≤ (5666113148373/50000000000000 : ℝ)^3463 := by
    have hnat : (232833009 : ℕ)^4487*50000000000000^3463 ≤ 5666113148373^3463*1250000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      232833009 1250000000 5666113148373 50000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5404672799/10000000000 : ℝ)^4487 ≤ (9011145832561/20000000000000 : ℝ)^3463 := by
    have hnat : (5404672799 : ℕ)^4487*20000000000000^3463 ≤ 9011145832561^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404672799 10000000000 9011145832561 20000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527052169/1000000000 : ℝ), (-232833009/1250000000 : ℝ), (5404672799/10000000000 : ℝ)] ![(10903011132029/25000000000000 : ℝ), (5666113148373/50000000000000 : ℝ), (9011145832561/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527052169/1000000000 : ℝ)|^4487 ≤ (10903011132029/25000000000000 : ℝ)^3463
        have hw : |(527052169/1000000000 : ℝ)|=(527052169/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-232833009/1250000000 : ℝ)|^4487 ≤ (5666113148373/50000000000000 : ℝ)^3463
        have hw : |(-232833009/1250000000 : ℝ)|=(232833009/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5404672799/10000000000 : ℝ)|^4487 ≤ (9011145832561/20000000000000 : ℝ)^3463
        have hw : |(5404672799/10000000000 : ℝ)|=(5404672799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_box_2 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270521953/10000000000 : ℝ)*x 0 + (5404673223/10000000000 : ℝ)*x 1 + (-1862663133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270521953/10000000000 : ℝ)^4487 ≤ (10903011836969/25000000000000 : ℝ)^3463 := by
    have hnat : (5270521953 : ℕ)^4487*25000000000000^3463 ≤ 10903011836969^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270521953 10000000000 10903011836969 25000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5404673223/10000000000 : ℝ)^4487 ≤ (22527866871321/50000000000000 : ℝ)^3463 := by
    have hnat : (5404673223 : ℕ)^4487*50000000000000^3463 ≤ 22527866871321^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404673223 10000000000 22527866871321 50000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1862663133/10000000000 : ℝ)^4487 ≤ (11332218894733/100000000000000 : ℝ)^3463 := by
    have hnat : (1862663133 : ℕ)^4487*100000000000000^3463 ≤ 11332218894733^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1862663133 10000000000 11332218894733 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270521953/10000000000 : ℝ), (5404673223/10000000000 : ℝ), (-1862663133/10000000000 : ℝ)] ![(10903011836969/25000000000000 : ℝ), (22527866871321/50000000000000 : ℝ), (11332218894733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270521953/10000000000 : ℝ)|^4487 ≤ (10903011836969/25000000000000 : ℝ)^3463
        have hw : |(5270521953/10000000000 : ℝ)|=(5270521953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5404673223/10000000000 : ℝ)|^4487 ≤ (22527866871321/50000000000000 : ℝ)^3463
        have hw : |(5404673223/10000000000 : ℝ)|=(5404673223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1862663133/10000000000 : ℝ)|^4487 ≤ (11332218894733/100000000000000 : ℝ)^3463
        have hw : |(-1862663133/10000000000 : ℝ)|=(1862663133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_box_3 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2240806887/5000000000 : ℝ)*x 0 + (1045730119/2500000000 : ℝ)*x 1 + (4182920981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2240806887/5000000000 : ℝ)^4487 ≤ (35347971980091/100000000000000 : ℝ)^3463 := by
    have hnat : (2240806887 : ℕ)^4487*100000000000000^3463 ≤ 35347971980091^3463*5000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240806887 5000000000 35347971980091 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1045730119/2500000000 : ℝ)^4487 ≤ (1010187858661/3125000000000 : ℝ)^3463 := by
    have hnat : (1045730119 : ℕ)^4487*3125000000000^3463 ≤ 1010187858661^3463*2500000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045730119 2500000000 1010187858661 3125000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4182920981/10000000000 : ℝ)^4487 ≤ (6465203306771/20000000000000 : ℝ)^3463 := by
    have hnat : (4182920981 : ℕ)^4487*20000000000000^3463 ≤ 6465203306771^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4182920981 10000000000 6465203306771 20000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2240806887/5000000000 : ℝ), (1045730119/2500000000 : ℝ), (4182920981/10000000000 : ℝ)] ![(35347971980091/100000000000000 : ℝ), (1010187858661/3125000000000 : ℝ), (6465203306771/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2240806887/5000000000 : ℝ)|^4487 ≤ (35347971980091/100000000000000 : ℝ)^3463
        have hw : |(2240806887/5000000000 : ℝ)|=(2240806887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1045730119/2500000000 : ℝ)|^4487 ≤ (1010187858661/3125000000000 : ℝ)^3463
        have hw : |(1045730119/2500000000 : ℝ)|=(1045730119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4182920981/10000000000 : ℝ)|^4487 ≤ (6465203306771/20000000000000 : ℝ)^3463
        have hw : |(4182920981/10000000000 : ℝ)|=(4182920981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_box_4 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2115597113/10000000000 : ℝ)*x 0 + (5243033499/10000000000 : ℝ)*x 1 + (1310758377/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2115597113/10000000000 : ℝ)^4487 ≤ (3341221558553/25000000000000 : ℝ)^3463 := by
    have hnat : (2115597113 : ℕ)^4487*25000000000000^3463 ≤ 3341221558553^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115597113 10000000000 3341221558553 25000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243033499/10000000000 : ℝ)^4487 ≤ (4331755683139/10000000000000 : ℝ)^3463 := by
    have hnat : (5243033499 : ℕ)^4487*10000000000000^3463 ≤ 4331755683139^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243033499 10000000000 4331755683139 10000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310758377/2500000000 : ℝ)^4487 ≤ (8663511385547/20000000000000 : ℝ)^3463 := by
    have hnat : (1310758377 : ℕ)^4487*20000000000000^3463 ≤ 8663511385547^3463*2500000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310758377 2500000000 8663511385547 20000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2115597113/10000000000 : ℝ), (5243033499/10000000000 : ℝ), (1310758377/2500000000 : ℝ)] ![(3341221558553/25000000000000 : ℝ), (4331755683139/10000000000000 : ℝ), (8663511385547/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2115597113/10000000000 : ℝ)|^4487 ≤ (3341221558553/25000000000000 : ℝ)^3463
        have hw : |(-2115597113/10000000000 : ℝ)|=(2115597113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243033499/10000000000 : ℝ)|^4487 ≤ (4331755683139/10000000000000 : ℝ)^3463
        have hw : |(5243033499/10000000000 : ℝ)|=(5243033499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310758377/2500000000 : ℝ)|^4487 ≤ (8663511385547/20000000000000 : ℝ)^3463
        have hw : |(1310758377/2500000000 : ℝ)|=(1310758377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_box_5 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1345801909/2500000000 : ℝ)*x 0 + (-964535017/5000000000 : ℝ)*x 1 + (5243033643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345801909/2500000000 : ℝ)^4487 ≤ (44824009410393/100000000000000 : ℝ)^3463 := by
    have hnat : (1345801909 : ℕ)^4487*100000000000000^3463 ≤ 44824009410393^3463*2500000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345801909 2500000000 44824009410393 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (964535017/5000000000 : ℝ)^4487 ≤ (5929216099009/50000000000000 : ℝ)^3463 := by
    have hnat : (964535017 : ℕ)^4487*50000000000000^3463 ≤ 5929216099009^3463*5000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      964535017 5000000000 5929216099009 50000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243033643/10000000000 : ℝ)^4487 ≤ (5414694796613/12500000000000 : ℝ)^3463 := by
    have hnat : (5243033643 : ℕ)^4487*12500000000000^3463 ≤ 5414694796613^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243033643 10000000000 5414694796613 12500000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1345801909/2500000000 : ℝ), (-964535017/5000000000 : ℝ), (5243033643/10000000000 : ℝ)] ![(44824009410393/100000000000000 : ℝ), (5929216099009/50000000000000 : ℝ), (5414694796613/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1345801909/2500000000 : ℝ)|^4487 ≤ (44824009410393/100000000000000 : ℝ)^3463
        have hw : |(1345801909/2500000000 : ℝ)|=(1345801909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-964535017/5000000000 : ℝ)|^4487 ≤ (5929216099009/50000000000000 : ℝ)^3463
        have hw : |(-964535017/5000000000 : ℝ)|=(964535017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243033643/10000000000 : ℝ)|^4487 ≤ (5414694796613/12500000000000 : ℝ)^3463
        have hw : |(5243033643/10000000000 : ℝ)|=(5243033643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_box_6 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (269160381/500000000 : ℝ)*x 0 + (2621516961/5000000000 : ℝ)*x 1 + (-1929069681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269160381/500000000 : ℝ)^4487 ≤ (11206002309443/25000000000000 : ℝ)^3463 := by
    have hnat : (269160381 : ℕ)^4487*25000000000000^3463 ≤ 11206002309443^3463*500000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269160381 500000000 11206002309443 25000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621516961/5000000000 : ℝ)^4487 ≤ (43317561359587/100000000000000 : ℝ)^3463 := by
    have hnat : (2621516961 : ℕ)^4487*100000000000000^3463 ≤ 43317561359587^3463*5000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621516961 5000000000 43317561359587 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1929069681/10000000000 : ℝ)^4487 ≤ (1482303673299/12500000000000 : ℝ)^3463 := by
    have hnat : (1929069681 : ℕ)^4487*12500000000000^3463 ≤ 1482303673299^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1929069681 10000000000 1482303673299 12500000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269160381/500000000 : ℝ), (2621516961/5000000000 : ℝ), (-1929069681/10000000000 : ℝ)] ![(11206002309443/25000000000000 : ℝ), (43317561359587/100000000000000 : ℝ), (1482303673299/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269160381/500000000 : ℝ)|^4487 ≤ (11206002309443/25000000000000 : ℝ)^3463
        have hw : |(269160381/500000000 : ℝ)|=(269160381/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621516961/5000000000 : ℝ)|^4487 ≤ (43317561359587/100000000000000 : ℝ)^3463
        have hw : |(2621516961/5000000000 : ℝ)|=(2621516961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1929069681/10000000000 : ℝ)|^4487 ≤ (1482303673299/12500000000000 : ℝ)^3463
        have hw : |(-1929069681/10000000000 : ℝ)|=(1929069681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_box_7 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4071562443/10000000000 : ℝ)*x 0 + (2193904827/5000000000 : ℝ)*x 1 + (438781003/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4071562443/10000000000 : ℝ)^4487 ≤ (15607684830041/50000000000000 : ℝ)^3463 := by
    have hnat : (4071562443 : ℕ)^4487*50000000000000^3463 ≤ 15607684830041^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4071562443 10000000000 15607684830041 50000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2193904827/5000000000 : ℝ)^4487 ≤ (4299039156647/12500000000000 : ℝ)^3463 := by
    have hnat : (2193904827 : ℕ)^4487*12500000000000^3463 ≤ 4299039156647^3463*5000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2193904827 5000000000 4299039156647 12500000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (438781003/1000000000 : ℝ)^4487 ≤ (34392317071783/100000000000000 : ℝ)^3463 := by
    have hnat : (438781003 : ℕ)^4487*100000000000000^3463 ≤ 34392317071783^3463*1000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438781003 1000000000 34392317071783 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4071562443/10000000000 : ℝ), (2193904827/5000000000 : ℝ), (438781003/1000000000 : ℝ)] ![(15607684830041/50000000000000 : ℝ), (4299039156647/12500000000000 : ℝ), (34392317071783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4071562443/10000000000 : ℝ)|^4487 ≤ (15607684830041/50000000000000 : ℝ)^3463
        have hw : |(4071562443/10000000000 : ℝ)|=(4071562443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2193904827/5000000000 : ℝ)|^4487 ≤ (4299039156647/12500000000000 : ℝ)^3463
        have hw : |(2193904827/5000000000 : ℝ)|=(2193904827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(438781003/1000000000 : ℝ)|^4487 ≤ (34392317071783/100000000000000 : ℝ)^3463
        have hw : |(438781003/1000000000 : ℝ)|=(438781003/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_box_8 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2022943599/10000000000 : ℝ)*x 0 + (2564991499/5000000000 : ℝ)*x 1 + (2712587911/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2022943599/10000000000 : ℝ)^4487 ≤ (12611449360273/100000000000000 : ℝ)^3463 := by
    have hnat : (2022943599 : ℕ)^4487*100000000000000^3463 ≤ 12611449360273^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2022943599 10000000000 12611449360273 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2564991499/5000000000 : ℝ)^4487 ≤ (42111233890233/100000000000000 : ℝ)^3463 := by
    have hnat : (2564991499 : ℕ)^4487*100000000000000^3463 ≤ 42111233890233^3463*5000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564991499 5000000000 42111233890233 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712587911/5000000000 : ℝ)^4487 ≤ (45277316731709/100000000000000 : ℝ)^3463 := by
    have hnat : (2712587911 : ℕ)^4487*100000000000000^3463 ≤ 45277316731709^3463*5000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712587911 5000000000 45277316731709 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2022943599/10000000000 : ℝ), (2564991499/5000000000 : ℝ), (2712587911/5000000000 : ℝ)] ![(12611449360273/100000000000000 : ℝ), (42111233890233/100000000000000 : ℝ), (45277316731709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2022943599/10000000000 : ℝ)|^4487 ≤ (12611449360273/100000000000000 : ℝ)^3463
        have hw : |(-2022943599/10000000000 : ℝ)|=(2022943599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2564991499/5000000000 : ℝ)|^4487 ≤ (42111233890233/100000000000000 : ℝ)^3463
        have hw : |(2564991499/5000000000 : ℝ)|=(2564991499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712587911/5000000000 : ℝ)|^4487 ≤ (45277316731709/100000000000000 : ℝ)^3463
        have hw : |(2712587911/5000000000 : ℝ)|=(2712587911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_box_9 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051244389/2000000000 : ℝ)*x 0 + (-1853989713/10000000000 : ℝ)*x 1 + (5425175601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051244389/2000000000 : ℝ)^4487 ≤ (5432348880557/12500000000000 : ℝ)^3463 := by
    have hnat : (1051244389 : ℕ)^4487*12500000000000^3463 ≤ 5432348880557^3463*2000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051244389 2000000000 5432348880557 12500000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1853989713/10000000000 : ℝ)^4487 ≤ (11263894598093/100000000000000 : ℝ)^3463 := by
    have hnat : (1853989713 : ℕ)^4487*100000000000000^3463 ≤ 11263894598093^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1853989713 10000000000 11263894598093 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5425175601/10000000000 : ℝ)^4487 ≤ (45277314341903/100000000000000 : ℝ)^3463 := by
    have hnat : (5425175601 : ℕ)^4487*100000000000000^3463 ≤ 45277314341903^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425175601 10000000000 45277314341903 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051244389/2000000000 : ℝ), (-1853989713/10000000000 : ℝ), (5425175601/10000000000 : ℝ)] ![(5432348880557/12500000000000 : ℝ), (11263894598093/100000000000000 : ℝ), (45277314341903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051244389/2000000000 : ℝ)|^4487 ≤ (5432348880557/12500000000000 : ℝ)^3463
        have hw : |(1051244389/2000000000 : ℝ)|=(1051244389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1853989713/10000000000 : ℝ)|^4487 ≤ (11263894598093/100000000000000 : ℝ)^3463
        have hw : |(-1853989713/10000000000 : ℝ)|=(1853989713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5425175601/10000000000 : ℝ)|^4487 ≤ (45277314341903/100000000000000 : ℝ)^3463
        have hw : |(5425175601/10000000000 : ℝ)|=(5425175601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_box_10 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314055361/2500000000 : ℝ)*x 0 + (5425176361/10000000000 : ℝ)*x 1 + (-1853989351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314055361/2500000000 : ℝ)^4487 ≤ (43458785677287/100000000000000 : ℝ)^3463 := by
    have hnat : (1314055361 : ℕ)^4487*100000000000000^3463 ≤ 43458785677287^3463*2500000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314055361 2500000000 43458785677287 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5425176361/10000000000 : ℝ)^4487 ≤ (22638661280121/50000000000000 : ℝ)^3463 := by
    have hnat : (5425176361 : ℕ)^4487*50000000000000^3463 ≤ 22638661280121^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425176361 10000000000 22638661280121 50000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1853989351/10000000000 : ℝ)^4487 ≤ (11263891748431/100000000000000 : ℝ)^3463 := by
    have hnat : (1853989351 : ℕ)^4487*100000000000000^3463 ≤ 11263891748431^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1853989351 10000000000 11263891748431 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314055361/2500000000 : ℝ), (5425176361/10000000000 : ℝ), (-1853989351/10000000000 : ℝ)] ![(43458785677287/100000000000000 : ℝ), (22638661280121/50000000000000 : ℝ), (11263891748431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314055361/2500000000 : ℝ)|^4487 ≤ (43458785677287/100000000000000 : ℝ)^3463
        have hw : |(1314055361/2500000000 : ℝ)|=(1314055361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5425176361/10000000000 : ℝ)|^4487 ≤ (22638661280121/50000000000000 : ℝ)^3463
        have hw : |(5425176361/10000000000 : ℝ)|=(5425176361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1853989351/10000000000 : ℝ)|^4487 ≤ (11263891748431/100000000000000 : ℝ)^3463
        have hw : |(-1853989351/10000000000 : ℝ)|=(1853989351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_box_11 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (566558977/1250000000 : ℝ)*x 0 + (166276021/400000000 : ℝ)*x 1 + (4156900187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (566558977/1250000000 : ℝ)^4487 ≤ (2241786891331/6250000000000 : ℝ)^3463 := by
    have hnat : (566558977 : ℕ)^4487*6250000000000^3463 ≤ 2241786891331^3463*1250000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566558977 1250000000 2241786891331 6250000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (166276021/400000000 : ℝ)^4487 ≤ (6413141311159/20000000000000 : ℝ)^3463 := by
    have hnat : (166276021 : ℕ)^4487*20000000000000^3463 ≤ 6413141311159^3463*400000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166276021 400000000 6413141311159 20000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4156900187/10000000000 : ℝ)^4487 ≤ (8016425794387/25000000000000 : ℝ)^3463 := by
    have hnat : (4156900187 : ℕ)^4487*25000000000000^3463 ≤ 8016425794387^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4156900187 10000000000 8016425794387 25000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(566558977/1250000000 : ℝ), (166276021/400000000 : ℝ), (4156900187/10000000000 : ℝ)] ![(2241786891331/6250000000000 : ℝ), (6413141311159/20000000000000 : ℝ), (8016425794387/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(566558977/1250000000 : ℝ)|^4487 ≤ (2241786891331/6250000000000 : ℝ)^3463
        have hw : |(566558977/1250000000 : ℝ)|=(566558977/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(166276021/400000000 : ℝ)|^4487 ≤ (6413141311159/20000000000000 : ℝ)^3463
        have hw : |(166276021/400000000 : ℝ)|=(166276021/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4156900187/10000000000 : ℝ)|^4487 ≤ (8016425794387/25000000000000 : ℝ)^3463
        have hw : |(4156900187/10000000000 : ℝ)|=(4156900187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_box_12 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-884703397/5000000000 : ℝ)*x 0 + (1102805881/2000000000 : ℝ)*x 1 + (5228023137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (884703397/5000000000 : ℝ)^4487 ≤ (2120519696597/20000000000000 : ℝ)^3463 := by
    have hnat : (884703397 : ℕ)^4487*20000000000000^3463 ≤ 2120519696597^3463*5000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884703397 5000000000 2120519696597 20000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1102805881/2000000000 : ℝ)^4487 ≤ (4624046187681/10000000000000 : ℝ)^3463 := by
    have hnat : (1102805881 : ℕ)^4487*10000000000000^3463 ≤ 4624046187681^3463*2000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102805881 2000000000 4624046187681 10000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5228023137/10000000000 : ℝ)^4487 ≤ (43156939622287/100000000000000 : ℝ)^3463 := by
    have hnat : (5228023137 : ℕ)^4487*100000000000000^3463 ≤ 43156939622287^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228023137 10000000000 43156939622287 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-884703397/5000000000 : ℝ), (1102805881/2000000000 : ℝ), (5228023137/10000000000 : ℝ)] ![(2120519696597/20000000000000 : ℝ), (4624046187681/10000000000000 : ℝ), (43156939622287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-884703397/5000000000 : ℝ)|^4487 ≤ (2120519696597/20000000000000 : ℝ)^3463
        have hw : |(-884703397/5000000000 : ℝ)|=(884703397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1102805881/2000000000 : ℝ)|^4487 ≤ (4624046187681/10000000000000 : ℝ)^3463
        have hw : |(1102805881/2000000000 : ℝ)|=(1102805881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5228023137/10000000000 : ℝ)|^4487 ≤ (43156939622287/100000000000000 : ℝ)^3463
        have hw : |(5228023137/10000000000 : ℝ)|=(5228023137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_box_13 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5393671913/10000000000 : ℝ)*x 0 + (-1935055879/10000000000 : ℝ)*x 1 + (5228022253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5393671913/10000000000 : ℝ)^4487 ≤ (44936938835089/100000000000000 : ℝ)^3463 := by
    have hnat : (5393671913 : ℕ)^4487*100000000000000^3463 ≤ 44936938835089^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393671913 10000000000 44936938835089 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1935055879/10000000000 : ℝ)^4487 ≤ (11906130989479/100000000000000 : ℝ)^3463 := by
    have hnat : (1935055879 : ℕ)^4487*100000000000000^3463 ≤ 11906130989479^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1935055879 10000000000 11906130989479 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5228022253/10000000000 : ℝ)^4487 ≤ (345255441337/800000000000 : ℝ)^3463 := by
    have hnat : (5228022253 : ℕ)^4487*800000000000^3463 ≤ 345255441337^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228022253 10000000000 345255441337 800000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5393671913/10000000000 : ℝ), (-1935055879/10000000000 : ℝ), (5228022253/10000000000 : ℝ)] ![(44936938835089/100000000000000 : ℝ), (11906130989479/100000000000000 : ℝ), (345255441337/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5393671913/10000000000 : ℝ)|^4487 ≤ (44936938835089/100000000000000 : ℝ)^3463
        have hw : |(5393671913/10000000000 : ℝ)|=(5393671913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1935055879/10000000000 : ℝ)|^4487 ≤ (11906130989479/100000000000000 : ℝ)^3463
        have hw : |(-1935055879/10000000000 : ℝ)|=(1935055879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5228022253/10000000000 : ℝ)|^4487 ≤ (345255441337/800000000000 : ℝ)^3463
        have hw : |(5228022253/10000000000 : ℝ)|=(5228022253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_box_14 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (337104463/625000000 : ℝ)*x 0 + (653502881/1250000000 : ℝ)*x 1 + (-241881937/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (337104463/625000000 : ℝ)^4487 ≤ (8987386676723/20000000000000 : ℝ)^3463 := by
    have hnat : (337104463 : ℕ)^4487*20000000000000^3463 ≤ 8987386676723^3463*625000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337104463 625000000 8987386676723 20000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (653502881/1250000000 : ℝ)^4487 ≤ (43156938670353/100000000000000 : ℝ)^3463 := by
    have hnat : (653502881 : ℕ)^4487*100000000000000^3463 ≤ 43156938670353^3463*1250000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653502881 1250000000 43156938670353 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (241881937/1250000000 : ℝ)^4487 ≤ (2976531984027/25000000000000 : ℝ)^3463 := by
    have hnat : (241881937 : ℕ)^4487*25000000000000^3463 ≤ 2976531984027^3463*1250000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241881937 1250000000 2976531984027 25000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(337104463/625000000 : ℝ), (653502881/1250000000 : ℝ), (-241881937/1250000000 : ℝ)] ![(8987386676723/20000000000000 : ℝ), (43156938670353/100000000000000 : ℝ), (2976531984027/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(337104463/625000000 : ℝ)|^4487 ≤ (8987386676723/20000000000000 : ℝ)^3463
        have hw : |(337104463/625000000 : ℝ)|=(337104463/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(653502881/1250000000 : ℝ)|^4487 ≤ (43156938670353/100000000000000 : ℝ)^3463
        have hw : |(653502881/1250000000 : ℝ)|=(653502881/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-241881937/1250000000 : ℝ)|^4487 ≤ (2976531984027/25000000000000 : ℝ)^3463
        have hw : |(-241881937/1250000000 : ℝ)|=(241881937/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_box_15 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2016311769/5000000000 : ℝ)*x 0 + (4406815117/10000000000 : ℝ)*x 1 + (2203406671/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2016311769/5000000000 : ℝ)^4487 ≤ (7707277624277/25000000000000 : ℝ)^3463 := by
    have hnat : (2016311769 : ℕ)^4487*25000000000000^3463 ≤ 7707277624277^3463*5000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016311769 5000000000 7707277624277 25000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4406815117/10000000000 : ℝ)^4487 ≤ (6917090754031/20000000000000 : ℝ)^3463 := by
    have hnat : (4406815117 : ℕ)^4487*20000000000000^3463 ≤ 6917090754031^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4406815117 10000000000 6917090754031 20000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2203406671/5000000000 : ℝ)^4487 ≤ (34585435720431/100000000000000 : ℝ)^3463 := by
    have hnat : (2203406671 : ℕ)^4487*100000000000000^3463 ≤ 34585435720431^3463*5000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203406671 5000000000 34585435720431 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2016311769/5000000000 : ℝ), (4406815117/10000000000 : ℝ), (2203406671/5000000000 : ℝ)] ![(7707277624277/25000000000000 : ℝ), (6917090754031/20000000000000 : ℝ), (34585435720431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2016311769/5000000000 : ℝ)|^4487 ≤ (7707277624277/25000000000000 : ℝ)^3463
        have hw : |(2016311769/5000000000 : ℝ)|=(2016311769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4406815117/10000000000 : ℝ)|^4487 ≤ (6917090754031/20000000000000 : ℝ)^3463
        have hw : |(4406815117/10000000000 : ℝ)|=(4406815117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2203406671/5000000000 : ℝ)|^4487 ≤ (34585435720431/100000000000000 : ℝ)^3463
        have hw : |(2203406671/5000000000 : ℝ)|=(2203406671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1495_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40505603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10849/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31859/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14637/25000 : ℝ) ∧ (16027/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (21473/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15479/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10849/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15479/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10849/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15479/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10849/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15479/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10849/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15479/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10849/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15479/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10849/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10849/100000 : ℝ) ^ (4485/1024 : ℝ) ≤ (2979133539613993/50000000000000000000 : ℝ) := by
    have hpowers : (10849/100000 : ℝ)^4485 ≤ (2979133539613993/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10849 : ℕ)^4485*50000000000000000000^1024 ≤ 2979133539613993^1024*100000^4485 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10849 100000 2979133539613993 50000000000000000000 4485 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10849/100000 : ℝ)) (X := (2979133539613993/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4485 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15479/100000 : ℝ) ^ (4485/1024 : ℝ) ≤ (5651957021374839/20000000000000000000 : ℝ) := by
    have hpowers : (15479/100000 : ℝ)^4485 ≤ (5651957021374839/20000000000000000000 : ℝ)^1024 := by
      have hnat : (15479 : ℕ)^4485*20000000000000000000^1024 ≤ 5651957021374839^1024*100000^4485 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15479 100000 5651957021374839 20000000000000000000 4485 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15479/100000 : ℝ)) (X := (5651957021374839/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4485 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002979133539613993/25000000000000000000 : ℝ) ≤ (10000272061760493/10000000000000000 : ℝ) ^ (4485/1024 : ℝ) := by
    have hpowers : (25002979133539613993/25000000000000000000 : ℝ)^1024 ≤ (10000272061760493/10000000000000000 : ℝ)^4485 := by
      have hnat : (25002979133539613993 : ℕ)^1024*10000000000000000^4485 ≤ 10000272061760493^4485*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002979133539613993 25000000000000000000 10000272061760493 10000000000000000 1024 4485 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000272061760493/10000000000000000 : ℝ)) (X := (25002979133539613993/25000000000000000000 : ℝ)) (by norm_num) 4485 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100034218052186102181/100000000000000000000 : ℝ) ≤ (10000781151844449/10000000000000000 : ℝ) ^ (4485/1024 : ℝ) := by
    have hpowers : (100034218052186102181/100000000000000000000 : ℝ)^1024 ≤ (10000781151844449/10000000000000000 : ℝ)^4485 := by
      have hnat : (100034218052186102181 : ℕ)^1024*10000000000000000^4485 ≤ 10000781151844449^4485*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100034218052186102181 100000000000000000000 10000781151844449 10000000000000000 1024 4485 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000781151844449/10000000000000000 : ℝ)) (X := (100034218052186102181/100000000000000000000 : ℝ)) (by norm_num) 4485 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005651957021374839/10000000000000000000 : ℝ) ≤ (2000258048385681/2000000000000000 : ℝ) ^ (4485/1024 : ℝ) := by
    have hpowers : (10005651957021374839/10000000000000000000 : ℝ)^1024 ≤ (2000258048385681/2000000000000000 : ℝ)^4485 := by
      have hnat : (10005651957021374839 : ℕ)^1024*2000000000000000^4485 ≤ 2000258048385681^4485*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005651957021374839 10000000000000000000 2000258048385681 2000000000000000 1024 4485 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000258048385681/2000000000000000 : ℝ)) (X := (10005651957021374839/10000000000000000000 : ℝ)) (by norm_num) 4485 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2979133539613993/50000000000000000000 : ℝ) ≤ ((23145106704654702651/23150000000000000000 : ℝ)+2*(127272520989/115750000000000 : ℝ)*(10849/100000 : ℝ))^(4485/1024 : ℝ) := by
    rw [show (23145106704654702651/23150000000000000000 : ℝ)+2*(127272520989/115750000000000 : ℝ)*(10849/100000 : ℝ)=(10000272061760493/10000000000000000 : ℝ) by norm_num, show 1+2*(2979133539613993/50000000000000000000 : ℝ)=(25002979133539613993/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5651957021374839/20000000000000000000 : ℝ)+(2979133539613993/50000000000000000000 : ℝ) ≤ ((23145106704654702651/23150000000000000000 : ℝ)+(127272520989/115750000000000 : ℝ)*((15479/100000 : ℝ)+(10849/100000 : ℝ)))^(4485/1024 : ℝ) := by
    rw [show (23145106704654702651/23150000000000000000 : ℝ)+(127272520989/115750000000000 : ℝ)*((15479/100000 : ℝ)+(10849/100000 : ℝ))=(10000781151844449/10000000000000000 : ℝ) by norm_num, show 1+(5651957021374839/20000000000000000000 : ℝ)+(2979133539613993/50000000000000000000 : ℝ)=(100034218052186102181/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5651957021374839/20000000000000000000 : ℝ) ≤ ((23145106704654702651/23150000000000000000 : ℝ)+2*(127272520989/115750000000000 : ℝ)*(15479/100000 : ℝ))^(4485/1024 : ℝ) := by
    rw [show (23145106704654702651/23150000000000000000 : ℝ)+2*(127272520989/115750000000000 : ℝ)*(15479/100000 : ℝ)=(2000258048385681/2000000000000000 : ℝ) by norm_num, show 1+2*(5651957021374839/20000000000000000000 : ℝ)=(10005651957021374839/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23145106704654702651/23150000000000000000 : ℝ)*(X 1 0+X 2 0)+(127272520989/115750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4485/1024 : ℝ)) (lo := (10849/100000 : ℝ)) (hi := (15479/100000 : ℝ)) (c := (23145106704654702651/23150000000000000000 : ℝ)) (alpha := (127272520989/115750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23145106704654702651/23150000000000000000 : ℝ)*(X 0 1+X 2 1)+(127272520989/115750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4485/1024 : ℝ)) (lo := (10849/100000 : ℝ)) (hi := (15479/100000 : ℝ)) (c := (23145106704654702651/23150000000000000000 : ℝ)) (alpha := (127272520989/115750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23145106704654702651/23150000000000000000 : ℝ)*(X 0 2+X 1 2)+(127272520989/115750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4485/1024 : ℝ)) (lo := (10849/100000 : ℝ)) (hi := (15479/100000 : ℝ)) (c := (23145106704654702651/23150000000000000000 : ℝ)) (alpha := (127272520989/115750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1676709591/10000000000 : ℝ)*X 0 0+(675584231/1250000000 : ℝ)*X 0 1+(5404672119/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((527052169/1000000000 : ℝ)*X 1 0+(-232833009/1250000000 : ℝ)*X 1 1+(5404672799/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5270521953/10000000000 : ℝ)*X 2 0+(5404673223/10000000000 : ℝ)*X 2 1+(-1862663133/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2240806887/5000000000 : ℝ)*X 0 0+(1045730119/2500000000 : ℝ)*X 0 1+(4182920981/10000000000 : ℝ)*X 0 2+(2240806887/5000000000 : ℝ)*X 1 0+(1045730119/2500000000 : ℝ)*X 1 1+(4182920981/10000000000 : ℝ)*X 1 2+(2240806887/5000000000 : ℝ)*X 2 0+(1045730119/2500000000 : ℝ)*X 2 1+(4182920981/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2115597113/10000000000 : ℝ)*X 0 0+(5243033499/10000000000 : ℝ)*X 0 1+(1310758377/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1345801909/2500000000 : ℝ)*X 1 0+(-964535017/5000000000 : ℝ)*X 1 1+(5243033643/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((269160381/500000000 : ℝ)*X 2 0+(2621516961/5000000000 : ℝ)*X 2 1+(-1929069681/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4071562443/10000000000 : ℝ)*X 0 0+(2193904827/5000000000 : ℝ)*X 0 1+(438781003/1000000000 : ℝ)*X 0 2+(4071562443/10000000000 : ℝ)*X 1 0+(2193904827/5000000000 : ℝ)*X 1 1+(438781003/1000000000 : ℝ)*X 1 2+(4071562443/10000000000 : ℝ)*X 2 0+(2193904827/5000000000 : ℝ)*X 2 1+(438781003/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2022943599/10000000000 : ℝ)*X 0 0+(2564991499/5000000000 : ℝ)*X 0 1+(2712587911/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1051244389/2000000000 : ℝ)*X 1 0+(-1853989713/10000000000 : ℝ)*X 1 1+(5425175601/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1314055361/2500000000 : ℝ)*X 2 0+(5425176361/10000000000 : ℝ)*X 2 1+(-1853989351/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((566558977/1250000000 : ℝ)*X 0 0+(166276021/400000000 : ℝ)*X 0 1+(4156900187/10000000000 : ℝ)*X 0 2+(566558977/1250000000 : ℝ)*X 1 0+(166276021/400000000 : ℝ)*X 1 1+(4156900187/10000000000 : ℝ)*X 1 2+(566558977/1250000000 : ℝ)*X 2 0+(166276021/400000000 : ℝ)*X 2 1+(4156900187/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-884703397/5000000000 : ℝ)*X 0 0+(1102805881/2000000000 : ℝ)*X 0 1+(5228023137/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5393671913/10000000000 : ℝ)*X 1 0+(-1935055879/10000000000 : ℝ)*X 1 1+(5228022253/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((337104463/625000000 : ℝ)*X 2 0+(653502881/1250000000 : ℝ)*X 2 1+(-241881937/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2016311769/5000000000 : ℝ)*X 0 0+(4406815117/10000000000 : ℝ)*X 0 1+(2203406671/5000000000 : ℝ)*X 0 2+(2016311769/5000000000 : ℝ)*X 1 0+(4406815117/10000000000 : ℝ)*X 1 1+(2203406671/5000000000 : ℝ)*X 1 2+(2016311769/5000000000 : ℝ)*X 2 0+(4406815117/10000000000 : ℝ)*X 2 1+(2203406671/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31859/50000 : ℝ) ≤ (-1843776391984623655841578191/2893750000000000000000000000 : ℝ) := by norm_num
    linear_combination (71580327/100000000000000 : ℝ)*(upper0) + (39436553/50000000000000 : ℝ)*(lower2) + (81749/800000000000 : ℝ)*(lower3) + (29341473/100000000000000 : ℝ)*(upper5) + (1099094068629227/50000000000000 : ℝ)*(major0) + (1099094068629227/50000000000000 : ℝ)*(major1) + (1099094068629227/50000000000000 : ℝ)*(major2) + (20919857/12500000000000 : ℝ)*(sp3) + (3060896318047829/100000000000000 : ℝ)*(sp4) + (1530430991817441/50000000000000 : ℝ)*(sp5) + (765195481116017/25000000000000 : ℝ)*(sp6) + (1356718394057483/100000000000000 : ℝ)*(sp7) + (34334412947/100000000000000 : ℝ)*(sp13) + (1429919797/1250000000000 : ℝ)*(sp14) + (1356718561416339/100000000000000 : ℝ)*(f.failure) + (3060896318047829/100000000000000 : ℝ)*(f.sum) + (5258410947539/1446875000000000000000000000 : ℝ)*base65 + (483692502463919223/1157500000000000000000000000000000 : ℝ)*base68 + (3407151301431419223/1157500000000000000000000000000000 : ℝ)*base70 + (7369817594983580777/1157500000000000000000000000000000 : ℝ)*base71 + (94323357763763/11575000000000000000000000000 : ℝ)*base74 + (8436399596431080777/1157500000000000000000000000000000 : ℝ)*base75 + (13338911198856080777/1157500000000000000000000000000000 : ℝ)*base77 + (6342253169501419223/1157500000000000000000000000000000 : ℝ)*base80 + (31964630003419/5787500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (4752583/2500000000000000000000 : ℝ)*base90 + (4752583/2500000000000000000000 : ℝ)*base92 + (4752583/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (14637/25000 : ℝ) ≤ (677719779085538124237101666994879/1157500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (25581523/12500000000000 : ℝ)*(upper0) + (21274237/100000000000000 : ℝ)*(lower1) + (316795087/100000000000000 : ℝ)*(upper4) + (2273295759860657/100000000000000 : ℝ)*(major0) + (2273295759860657/100000000000000 : ℝ)*(major1) + (2273295759860657/100000000000000 : ℝ)*(major2) + (780995578643797/25000000000000 : ℝ)*(sp0) + (312399027428777/10000000000000 : ℝ)*(sp1) + (78099236307057/2500000000000 : ℝ)*(sp2) + (1403064280053957/100000000000000 : ℝ)*(sp3) + (1919783153/20000000000000 : ℝ)*(sp5) + (6084184251/20000000000000 : ℝ)*(sp6) + (10598167617/100000000000000 : ℝ)*(sp7) + (17558628347/100000000000000 : ℝ)*(sp8) + (701537439110787/50000000000000 : ℝ)*(f.failure) + (624799974640707/20000000000000 : ℝ)*(f.sum) + (7999476792027/5787500000000000000000000000 : ℝ)*base66 + (2891817244783101707/2315000000000000000000000000000000 : ℝ)*base67 + (10790934880588101707/2315000000000000000000000000000000 : ℝ)*base69 + (6337159692551898293/2315000000000000000000000000000000 : ℝ)*base72 + (74131095092727/5787500000000000000000000000 : ℝ)*base74 + (10109305079103101707/2315000000000000000000000000000000 : ℝ)*base75 + (4142051030948101707/2315000000000000000000000000000000 : ℝ)*base77 + (37123126333516898293/2315000000000000000000000000000000 : ℝ)*base80 + (11038884442073/5787500000000000000000000000 : ℝ)*base81 + (1260439/1250000000000000000000 : ℝ)*base90 + (1260439/1250000000000000000000 : ℝ)*base92 + (1260439/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (16027/20000 : ℝ) ≤ (927586029130491637765034629016931/1157500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (286359/25000000000000 : ℝ)*(upper0) + (4384113/10000000000000 : ℝ)*(upper1) + (8967631/50000000000000 : ℝ)*(upper4) + (2469143055242573/100000000000000 : ℝ)*(major0) + (2469143055242573/100000000000000 : ℝ)*(major1) + (2469143055242573/100000000000000 : ℝ)*(major2) + (666558573/50000000000000 : ℝ)*(sp0) + (26244539361/20000000000000 : ℝ)*(sp2) + (978657833/5000000000000 : ℝ)*(sp3) + (423452431752733/12500000000000 : ℝ)*(sp8) + (1693811111082857/50000000000000 : ℝ)*(sp9) + (338749099946891/10000000000000 : ℝ)*(sp10) + (761965987255531/50000000000000 : ℝ)*(sp11) + (89689169/6250000000000 : ℝ)*(sp12) + (761975773833861/50000000000000 : ℝ)*(f.failure) + (1693811111082857/50000000000000 : ℝ)*(f.sum) + (607185652289/2893750000000000000000000000 : ℝ)*base66 + (4335373800280561023/2315000000000000000000000000000000 : ℝ)*base67 + (3986845517470561023/2315000000000000000000000000000000 : ℝ)*base69 + (12729373386900561023/2315000000000000000000000000000000 : ℝ)*base71 + (5879889157353/5787500000000000000000000000 : ℝ)*base74 + (16331654588010561023/2315000000000000000000000000000000 : ℝ)*base75 + (7215213892724438977/2315000000000000000000000000000000 : ℝ)*base78 + (2041274774594438977/2315000000000000000000000000000000 : ℝ)*base80 + (56640288727469/11575000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (876817/1250000000000000000000 : ℝ)*base90 + (876817/1250000000000000000000 : ℝ)*base92 + (876817/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-21473/25000 : ℝ) ≤ (-4970846601984178844813970369/5787500000000000000000000000 : ℝ) := by norm_num
    linear_combination (165649909/100000000000000 : ℝ)*(lower0) + (5466911/5000000000000 : ℝ)*(upper1) + (4178119/20000000000000 : ℝ)*(lower2) + (82418101/100000000000000 : ℝ)*(upper3) + (5181531/5000000000000 : ℝ)*(upper5) + (626949608054533/25000000000000 : ℝ)*(major0) + (626949608054533/25000000000000 : ℝ)*(major1) + (626949608054533/25000000000000 : ℝ)*(major2) + (91602299/12500000000000 : ℝ)*(sp4) + (37739761111/20000000000000 : ℝ)*(sp5) + (1748208163419897/50000000000000 : ℝ)*(sp12) + (437028545106579/12500000000000 : ℝ)*(sp13) + (1748208529829093/50000000000000 : ℝ)*(sp14) + (309561918164523/20000000000000 : ℝ)*(sp15) + (309561918164523/20000000000000 : ℝ)*(f.failure) + (1748208529829093/50000000000000 : ℝ)*(f.sum) + (28640613013627/5787500000000000000000000000 : ℝ)*base66 + (6734895686111316983/578750000000000000000000000000000 : ℝ)*base67 + (661611765620066983/578750000000000000000000000000000 : ℝ)*base69 + (1523304114362433017/578750000000000000000000000000000 : ℝ)*base72 + (151184993697821/11575000000000000000000000000 : ℝ)*base73 + (73929623331183017/578750000000000000000000000000000 : ℝ)*base76 + (1740684288107433017/578750000000000000000000000000000 : ℝ)*base78 + (4055043149548816983/578750000000000000000000000000000 : ℝ)*base79 + (15769247731773/5787500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (2677631/500000000000000000000 : ℝ)*base90 + (2677631/500000000000000000000 : ℝ)*base92 + (2677631/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1495_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40505603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10849/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31859/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(14637/25000 : ℝ) else (16027/20000 : ℝ) ≤ X j i ∧ X j i ≤ (21473/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1495_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1495_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40505603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (387/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10847/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31859/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(14637/25000 : ℝ) else (16027/20000 : ℝ) ≤ X j i ∧ X j i ≤ (21473/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1495_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1495_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1495_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40505603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (387/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10847/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31859/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(14637/25000 : ℝ) else (16027/20000 : ℝ) ≤ X j i ∧ X j i ≤ (21473/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1495_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
