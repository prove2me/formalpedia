-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1374_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:21:27.143385+00:00
-- url     : https://prove2.me/submissions/b4b39b8c-f845-4706-884f-c00af30fecce

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
theorem support_rectangle_w1374_s6_0 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1008321529/5000000000 : ℝ)*x 0 + (1352766713/2500000000 : ℝ)*x 1 + (1049105919/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1008321529/5000000000 : ℝ)^2167 ≤ (12288679248779/100000000000000 : ℝ)^1655 := by
    have hnat : (1008321529 : ℕ)^2167*100000000000000^1655 ≤ 12288679248779^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008321529 5000000000 12288679248779 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352766713/2500000000 : ℝ)^2167 ≤ (22373803473423/50000000000000 : ℝ)^1655 := by
    have hnat : (1352766713 : ℕ)^2167*50000000000000^1655 ≤ 22373803473423^1655*2500000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352766713 2500000000 22373803473423 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049105919/2000000000 : ℝ)^2167 ≤ (42963713780641/100000000000000 : ℝ)^1655 := by
    have hnat : (1049105919 : ℕ)^2167*100000000000000^1655 ≤ 42963713780641^1655*2000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049105919 2000000000 42963713780641 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1008321529/5000000000 : ℝ), (1352766713/2500000000 : ℝ), (1049105919/2000000000 : ℝ)] ![(12288679248779/100000000000000 : ℝ), (22373803473423/50000000000000 : ℝ), (42963713780641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1008321529/5000000000 : ℝ)|^2167 ≤ (12288679248779/100000000000000 : ℝ)^1655
        have hw : |(-1008321529/5000000000 : ℝ)|=(1008321529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352766713/2500000000 : ℝ)|^2167 ≤ (22373803473423/50000000000000 : ℝ)^1655
        have hw : |(1352766713/2500000000 : ℝ)|=(1352766713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049105919/2000000000 : ℝ)|^2167 ≤ (42963713780641/100000000000000 : ℝ)^1655
        have hw : |(1049105919/2000000000 : ℝ)|=(1049105919/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s6_1 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (133710631/250000000 : ℝ)*x 0 + (-420192143/2000000000 : ℝ)*x 1 + (5245529791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133710631/250000000 : ℝ)^2167 ≤ (5508817759693/12500000000000 : ℝ)^1655 := by
    have hnat : (133710631 : ℕ)^2167*12500000000000^1655 ≤ 5508817759693^1655*250000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133710631 250000000 5508817759693 12500000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (420192143/2000000000 : ℝ)^2167 ≤ (12965742031113/100000000000000 : ℝ)^1655 := by
    have hnat : (420192143 : ℕ)^2167*100000000000000^1655 ≤ 12965742031113^1655*2000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420192143 2000000000 12965742031113 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245529791/10000000000 : ℝ)^2167 ≤ (343709727061/800000000000 : ℝ)^1655 := by
    have hnat : (5245529791 : ℕ)^2167*800000000000^1655 ≤ 343709727061^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245529791 10000000000 343709727061 800000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133710631/250000000 : ℝ), (-420192143/2000000000 : ℝ), (5245529791/10000000000 : ℝ)] ![(5508817759693/12500000000000 : ℝ), (12965742031113/100000000000000 : ℝ), (343709727061/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133710631/250000000 : ℝ)|^2167 ≤ (5508817759693/12500000000000 : ℝ)^1655
        have hw : |(133710631/250000000 : ℝ)|=(133710631/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-420192143/2000000000 : ℝ)|^2167 ≤ (12965742031113/100000000000000 : ℝ)^1655
        have hw : |(-420192143/2000000000 : ℝ)|=(420192143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245529791/10000000000 : ℝ)|^2167 ≤ (343709727061/800000000000 : ℝ)^1655
        have hw : |(5245529791/10000000000 : ℝ)|=(5245529791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s6_2 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1069685067/2000000000 : ℝ)*x 0 + (5245529383/10000000000 : ℝ)*x 1 + (-2100961129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069685067/2000000000 : ℝ)^2167 ≤ (5508817887813/12500000000000 : ℝ)^1655 := by
    have hnat : (1069685067 : ℕ)^2167*12500000000000^1655 ≤ 5508817887813^1655*2000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069685067 2000000000 5508817887813 12500000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245529383/10000000000 : ℝ)^2167 ≤ (21481855753533/50000000000000 : ℝ)^1655 := by
    have hnat : (5245529383 : ℕ)^2167*50000000000000^1655 ≤ 21481855753533^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245529383 10000000000 21481855753533 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2100961129/10000000000 : ℝ)^2167 ≤ (12965745376457/100000000000000 : ℝ)^1655 := by
    have hnat : (2100961129 : ℕ)^2167*100000000000000^1655 ≤ 12965745376457^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100961129 10000000000 12965745376457 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069685067/2000000000 : ℝ), (5245529383/10000000000 : ℝ), (-2100961129/10000000000 : ℝ)] ![(5508817887813/12500000000000 : ℝ), (21481855753533/50000000000000 : ℝ), (12965745376457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069685067/2000000000 : ℝ)|^2167 ≤ (5508817887813/12500000000000 : ℝ)^1655
        have hw : |(1069685067/2000000000 : ℝ)|=(1069685067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245529383/10000000000 : ℝ)|^2167 ≤ (21481855753533/50000000000000 : ℝ)^1655
        have hw : |(5245529383/10000000000 : ℝ)|=(5245529383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2100961129/10000000000 : ℝ)|^2167 ≤ (12965745376457/100000000000000 : ℝ)^1655
        have hw : |(-2100961129/10000000000 : ℝ)|=(2100961129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s6_3 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (863664001/2000000000 : ℝ)*x 0 + (4146150079/10000000000 : ℝ)*x 1 + (1124264633/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (863664001/2000000000 : ℝ)^2167 ≤ (1665189994231/5000000000000 : ℝ)^1655 := by
    have hnat : (863664001 : ℕ)^2167*5000000000000^1655 ≤ 1665189994231^1655*2000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863664001 2000000000 1665189994231 5000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4146150079/10000000000 : ℝ)^2167 ≤ (6315206431253/20000000000000 : ℝ)^1655 := by
    have hnat : (4146150079 : ℕ)^2167*20000000000000^1655 ≤ 6315206431253^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4146150079 10000000000 6315206431253 20000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124264633/2500000000 : ℝ)^2167 ≤ (4390020993509/12500000000000 : ℝ)^1655 := by
    have hnat : (1124264633 : ℕ)^2167*12500000000000^1655 ≤ 4390020993509^1655*2500000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124264633 2500000000 4390020993509 12500000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(863664001/2000000000 : ℝ), (4146150079/10000000000 : ℝ), (1124264633/2500000000 : ℝ)] ![(1665189994231/5000000000000 : ℝ), (6315206431253/20000000000000 : ℝ), (4390020993509/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(863664001/2000000000 : ℝ)|^2167 ≤ (1665189994231/5000000000000 : ℝ)^1655
        have hw : |(863664001/2000000000 : ℝ)|=(863664001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4146150079/10000000000 : ℝ)|^2167 ≤ (6315206431253/20000000000000 : ℝ)^1655
        have hw : |(4146150079/10000000000 : ℝ)|=(4146150079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1124264633/2500000000 : ℝ)|^2167 ≤ (4390020993509/12500000000000 : ℝ)^1655
        have hw : |(1124264633/2500000000 : ℝ)|=(1124264633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s6_4 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2016655259/10000000000 : ℝ)*x 0 + (5246123897/10000000000 : ℝ)*x 1 + (216418769/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2016655259/10000000000 : ℝ)^2167 ≤ (6144388299049/50000000000000 : ℝ)^1655 := by
    have hnat : (2016655259 : ℕ)^2167*50000000000000^1655 ≤ 6144388299049^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016655259 10000000000 6144388299049 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246123897/10000000000 : ℝ)^2167 ≤ (21485043715157/50000000000000 : ℝ)^1655 := by
    have hnat : (5246123897 : ℕ)^2167*50000000000000^1655 ≤ 21485043715157^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246123897 10000000000 21485043715157 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216418769/400000000 : ℝ)^2167 ≤ (8948227191697/20000000000000 : ℝ)^1655 := by
    have hnat : (216418769 : ℕ)^2167*20000000000000^1655 ≤ 8948227191697^1655*400000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216418769 400000000 8948227191697 20000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2016655259/10000000000 : ℝ), (5246123897/10000000000 : ℝ), (216418769/400000000 : ℝ)] ![(6144388299049/50000000000000 : ℝ), (21485043715157/50000000000000 : ℝ), (8948227191697/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2016655259/10000000000 : ℝ)|^2167 ≤ (6144388299049/50000000000000 : ℝ)^1655
        have hw : |(-2016655259/10000000000 : ℝ)|=(2016655259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246123897/10000000000 : ℝ)|^2167 ≤ (21485043715157/50000000000000 : ℝ)^1655
        have hw : |(5246123897/10000000000 : ℝ)|=(5246123897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216418769/400000000 : ℝ)|^2167 ≤ (8948227191697/20000000000000 : ℝ)^1655
        have hw : |(216418769/400000000 : ℝ)|=(216418769/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s6_5 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652816729/5000000000 : ℝ)*x 0 + (-484005391/2500000000 : ℝ)*x 1 + (5410469229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652816729/5000000000 : ℝ)^2167 ≤ (2725589478157/6250000000000 : ℝ)^1655 := by
    have hnat : (2652816729 : ℕ)^2167*6250000000000^1655 ≤ 2725589478157^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652816729 5000000000 2725589478157 6250000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (484005391/2500000000 : ℝ)^2167 ≤ (1164943232491/10000000000000 : ℝ)^1655 := by
    have hnat : (484005391 : ℕ)^2167*10000000000000^1655 ≤ 1164943232491^1655*2500000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      484005391 2500000000 1164943232491 10000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410469229/10000000000 : ℝ)^2167 ≤ (8948227200359/20000000000000 : ℝ)^1655 := by
    have hnat : (5410469229 : ℕ)^2167*20000000000000^1655 ≤ 8948227200359^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410469229 10000000000 8948227200359 20000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652816729/5000000000 : ℝ), (-484005391/2500000000 : ℝ), (5410469229/10000000000 : ℝ)] ![(2725589478157/6250000000000 : ℝ), (1164943232491/10000000000000 : ℝ), (8948227200359/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652816729/5000000000 : ℝ)|^2167 ≤ (2725589478157/6250000000000 : ℝ)^1655
        have hw : |(2652816729/5000000000 : ℝ)|=(2652816729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-484005391/2500000000 : ℝ)|^2167 ≤ (1164943232491/10000000000000 : ℝ)^1655
        have hw : |(-484005391/2500000000 : ℝ)|=(484005391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410469229/10000000000 : ℝ)|^2167 ≤ (8948227200359/20000000000000 : ℝ)^1655
        have hw : |(5410469229/10000000000 : ℝ)|=(5410469229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s6_6 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652816731/5000000000 : ℝ)*x 0 + (5410469227/10000000000 : ℝ)*x 1 + (-1936021563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652816731/5000000000 : ℝ)^2167 ≤ (21804715846781/50000000000000 : ℝ)^1655 := by
    have hnat : (2652816731 : ℕ)^2167*50000000000000^1655 ≤ 21804715846781^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652816731 5000000000 21804715846781 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410469227/10000000000 : ℝ)^2167 ≤ (2237056799007/5000000000000 : ℝ)^1655 := by
    have hnat : (5410469227 : ℕ)^2167*5000000000000^1655 ≤ 2237056799007^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410469227 10000000000 2237056799007 5000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1936021563/10000000000 : ℝ)^2167 ≤ (1456179039629/12500000000000 : ℝ)^1655 := by
    have hnat : (1936021563 : ℕ)^2167*12500000000000^1655 ≤ 1456179039629^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1936021563 10000000000 1456179039629 12500000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652816731/5000000000 : ℝ), (5410469227/10000000000 : ℝ), (-1936021563/10000000000 : ℝ)] ![(21804715846781/50000000000000 : ℝ), (2237056799007/5000000000000 : ℝ), (1456179039629/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652816731/5000000000 : ℝ)|^2167 ≤ (21804715846781/50000000000000 : ℝ)^1655
        have hw : |(2652816731/5000000000 : ℝ)|=(2652816731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410469227/10000000000 : ℝ)|^2167 ≤ (2237056799007/5000000000000 : ℝ)^1655
        have hw : |(5410469227/10000000000 : ℝ)|=(5410469227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1936021563/10000000000 : ℝ)|^2167 ≤ (1456179039629/12500000000000 : ℝ)^1655
        have hw : |(-1936021563/10000000000 : ℝ)|=(1936021563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s6_7 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2159172599/5000000000 : ℝ)*x 0 + (35966389/80000000 : ℝ)*x 1 + (2073708213/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2159172599/5000000000 : ℝ)^2167 ≤ (33304054286407/100000000000000 : ℝ)^1655 := by
    have hnat : (2159172599 : ℕ)^2167*100000000000000^1655 ≤ 33304054286407^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159172599 5000000000 33304054286407 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35966389/80000000 : ℝ)^2167 ≤ (140429140787/400000000000 : ℝ)^1655 := by
    have hnat : (35966389 : ℕ)^2167*400000000000^1655 ≤ 140429140787^1655*80000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35966389 80000000 140429140787 400000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2073708213/5000000000 : ℝ)^2167 ≤ (31588660508661/100000000000000 : ℝ)^1655 := by
    have hnat : (2073708213 : ℕ)^2167*100000000000000^1655 ≤ 31588660508661^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073708213 5000000000 31588660508661 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2159172599/5000000000 : ℝ), (35966389/80000000 : ℝ), (2073708213/5000000000 : ℝ)] ![(33304054286407/100000000000000 : ℝ), (140429140787/400000000000 : ℝ), (31588660508661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2159172599/5000000000 : ℝ)|^2167 ≤ (33304054286407/100000000000000 : ℝ)^1655
        have hw : |(2159172599/5000000000 : ℝ)|=(2159172599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(35966389/80000000 : ℝ)|^2167 ≤ (140429140787/400000000000 : ℝ)^1655
        have hw : |(35966389/80000000 : ℝ)|=(35966389/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2073708213/5000000000 : ℝ)|^2167 ≤ (31588660508661/100000000000000 : ℝ)^1655
        have hw : |(2073708213/5000000000 : ℝ)|=(2073708213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1374_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31198181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14733/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (701/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (5611/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14727/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14733/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (701/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14733/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (701/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14733/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (701/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14733/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (701/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14733/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (701/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14733/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (701/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (701/6250 : ℝ) ^ (4333/1024 : ℝ) ≤ (596103235341667/6250000000000000000 : ℝ) := by
    have hpowers : (701/6250 : ℝ)^4333 ≤ (596103235341667/6250000000000000000 : ℝ)^1024 := by
      have hnat : (701 : ℕ)^4333*6250000000000000000^1024 ≤ 596103235341667^1024*6250^4333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        701 6250 596103235341667 6250000000000000000 4333 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (701/6250 : ℝ)) (X := (596103235341667/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14733/100000 : ℝ) ^ (4333/1024 : ℝ) ≤ (7561529631450229/25000000000000000000 : ℝ) := by
    have hpowers : (14733/100000 : ℝ)^4333 ≤ (7561529631450229/25000000000000000000 : ℝ)^1024 := by
      have hnat : (14733 : ℕ)^4333*25000000000000000000^1024 ≤ 7561529631450229^1024*100000^4333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14733 100000 7561529631450229 25000000000000000000 4333 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14733/100000 : ℝ)) (X := (7561529631450229/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125596103235341667/3125000000000000000 : ℝ) ≤ (10000450765941617/10000000000000000 : ℝ) ^ (4333/1024 : ℝ) := by
    have hpowers : (3125596103235341667/3125000000000000000 : ℝ)^1024 ≤ (10000450765941617/10000000000000000 : ℝ)^4333 := by
      have hnat : (3125596103235341667 : ℕ)^1024*10000000000000000^4333 ≤ 10000450765941617^4333*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125596103235341667 3125000000000000000 10000450765941617 10000000000000000 1024 4333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000450765941617/10000000000000000 : ℝ)) (X := (3125596103235341667/3125000000000000000 : ℝ)) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25009945942572816897/25000000000000000000 : ℝ) ≤ (5000470025313419/5000000000000000 : ℝ) ^ (4333/1024 : ℝ) := by
    have hpowers : (25009945942572816897/25000000000000000000 : ℝ)^1024 ≤ (5000470025313419/5000000000000000 : ℝ)^4333 := by
      have hnat : (25009945942572816897 : ℕ)^1024*5000000000000000^4333 ≤ 5000470025313419^4333*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009945942572816897 25000000000000000000 5000470025313419 5000000000000000 1024 4333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000470025313419/5000000000000000 : ℝ)) (X := (25009945942572816897/25000000000000000000 : ℝ)) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507561529631450229/12500000000000000000 : ℝ) ≤ (10001429335312059/10000000000000000 : ℝ) ^ (4333/1024 : ℝ) := by
    have hpowers : (12507561529631450229/12500000000000000000 : ℝ)^1024 ≤ (10001429335312059/10000000000000000 : ℝ)^4333 := by
      have hnat : (12507561529631450229 : ℕ)^1024*10000000000000000^4333 ≤ 10001429335312059^4333*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507561529631450229 12500000000000000000 10001429335312059 10000000000000000 1024 4333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001429335312059/10000000000000000 : ℝ)) (X := (12507561529631450229/12500000000000000000 : ℝ)) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(596103235341667/6250000000000000000 : ℝ) ≤ ((35160609709757789517/35170000000000000000 : ℝ)+2*(489284685221/351700000000000 : ℝ)*(701/6250 : ℝ))^(4333/1024 : ℝ) := by
    rw [show (35160609709757789517/35170000000000000000 : ℝ)+2*(489284685221/351700000000000 : ℝ)*(701/6250 : ℝ)=(10000450765941617/10000000000000000 : ℝ) by norm_num, show 1+2*(596103235341667/6250000000000000000 : ℝ)=(3125596103235341667/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7561529631450229/25000000000000000000 : ℝ)+(596103235341667/6250000000000000000 : ℝ) ≤ ((35160609709757789517/35170000000000000000 : ℝ)+(489284685221/351700000000000 : ℝ)*((14733/100000 : ℝ)+(701/6250 : ℝ)))^(4333/1024 : ℝ) := by
    rw [show (35160609709757789517/35170000000000000000 : ℝ)+(489284685221/351700000000000 : ℝ)*((14733/100000 : ℝ)+(701/6250 : ℝ))=(5000470025313419/5000000000000000 : ℝ) by norm_num, show 1+(7561529631450229/25000000000000000000 : ℝ)+(596103235341667/6250000000000000000 : ℝ)=(25009945942572816897/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7561529631450229/25000000000000000000 : ℝ) ≤ ((35160609709757789517/35170000000000000000 : ℝ)+2*(489284685221/351700000000000 : ℝ)*(14733/100000 : ℝ))^(4333/1024 : ℝ) := by
    rw [show (35160609709757789517/35170000000000000000 : ℝ)+2*(489284685221/351700000000000 : ℝ)*(14733/100000 : ℝ)=(10001429335312059/10000000000000000 : ℝ) by norm_num, show 1+2*(7561529631450229/25000000000000000000 : ℝ)=(12507561529631450229/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35160609709757789517/35170000000000000000 : ℝ)*(X 1 0+X 2 0)+(489284685221/351700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4333/1024 : ℝ)) (lo := (701/6250 : ℝ)) (hi := (14733/100000 : ℝ)) (c := (35160609709757789517/35170000000000000000 : ℝ)) (alpha := (489284685221/351700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35160609709757789517/35170000000000000000 : ℝ)*(X 0 1+X 2 1)+(489284685221/351700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4333/1024 : ℝ)) (lo := (701/6250 : ℝ)) (hi := (14733/100000 : ℝ)) (c := (35160609709757789517/35170000000000000000 : ℝ)) (alpha := (489284685221/351700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35160609709757789517/35170000000000000000 : ℝ)*(X 0 2+X 1 2)+(489284685221/351700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4333/1024 : ℝ)) (lo := (701/6250 : ℝ)) (hi := (14733/100000 : ℝ)) (c := (35160609709757789517/35170000000000000000 : ℝ)) (alpha := (489284685221/351700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1008321529/5000000000 : ℝ)*X 0 0+(1352766713/2500000000 : ℝ)*X 0 1+(1049105919/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((133710631/250000000 : ℝ)*X 1 0+(-420192143/2000000000 : ℝ)*X 1 1+(5245529791/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069685067/2000000000 : ℝ)*X 2 0+(5245529383/10000000000 : ℝ)*X 2 1+(-2100961129/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((863664001/2000000000 : ℝ)*X 0 0+(4146150079/10000000000 : ℝ)*X 0 1+(1124264633/2500000000 : ℝ)*X 0 2+(863664001/2000000000 : ℝ)*X 1 0+(4146150079/10000000000 : ℝ)*X 1 1+(1124264633/2500000000 : ℝ)*X 1 2+(863664001/2000000000 : ℝ)*X 2 0+(4146150079/10000000000 : ℝ)*X 2 1+(1124264633/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2016655259/10000000000 : ℝ)*X 0 0+(5246123897/10000000000 : ℝ)*X 0 1+(216418769/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652816729/5000000000 : ℝ)*X 1 0+(-484005391/2500000000 : ℝ)*X 1 1+(5410469229/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652816731/5000000000 : ℝ)*X 2 0+(5410469227/10000000000 : ℝ)*X 2 1+(-1936021563/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2159172599/5000000000 : ℝ)*X 0 0+(35966389/80000000 : ℝ)*X 0 1+(2073708213/5000000000 : ℝ)*X 0 2+(2159172599/5000000000 : ℝ)*X 1 0+(35966389/80000000 : ℝ)*X 1 1+(2073708213/5000000000 : ℝ)*X 1 2+(2159172599/5000000000 : ℝ)*X 2 0+(35966389/80000000 : ℝ)*X 2 1+(2073708213/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11182393242660971523998820921/1758500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (100044849/10000000000000 : ℝ)*(base19) + (755534199/50000000000000 : ℝ)*(base23) + (1137061/3125000000000 : ℝ)*(upper3) + (58524869/25000000000000 : ℝ)*(lower4) + (889078753036387/20000000000000 : ℝ)*(major0) + (889078753036387/20000000000000 : ℝ)*(major1) + (277837110323871/6250000000000 : ℝ)*(major2) + (6040975973731513/100000000000000 : ℝ)*(sp0) + (3020504392163029/50000000000000 : ℝ)*(sp1) + (1510250994167957/25000000000000 : ℝ)*(sp2) + (1424881137548947/50000000000000 : ℝ)*(sp3) + (6762208607/20000000000000 : ℝ)*(sp4) + (4297034321/100000000000000 : ℝ)*(sp6) + (1907315377/12500000000000 : ℝ)*(sp7) + (284977753362091/10000000000000 : ℝ)*(f.failure) + (1510252446193637/25000000000000 : ℝ)*(f.sum) + (116596488286261/35170000000000000000000000000 : ℝ)*base65 + (1771471135284524921/703400000000000000000000000000000 : ℝ)*base68 + (1624818615257245943/219812500000000000000000000000000 : ℝ)*base70 + (3763956766151924921/703400000000000000000000000000000 : ℝ)*base72 + (920069186029/35170000000000000000000000000 : ℝ)*base74 + (4054377331323245943/219812500000000000000000000000000 : ℝ)*base76 + (3457837140352855079/703400000000000000000000000000000 : ℝ)*base77 + (1995545894556944921/703400000000000000000000000000000 : ℝ)*base80 + (747982104043/1758500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (3556471/200000000000000000000 : ℝ)*base89 + (3556471/200000000000000000000 : ℝ)*base91 + (1556471/200000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5664915411736470975685730427/879250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1111584057/100000000000000 : ℝ)*(base19) + (1212532501/100000000000000 : ℝ)*(base23) + (26666859/20000000000000 : ℝ)*(upper3) + (339653/781250000000 : ℝ)*(lower4) + (67497309/50000000000000 : ℝ)*(upper5) + (2238789586502077/50000000000000 : ℝ)*(major0) + (2238789586502077/50000000000000 : ℝ)*(major1) + (2238789586502077/50000000000000 : ℝ)*(major2) + (5748542177/25000000000000 : ℝ)*(sp1) + (24781856671/100000000000000 : ℝ)*(sp2) + (6084747723020273/100000000000000 : ℝ)*(sp4) + (1521180904316877/25000000000000 : ℝ)*(sp5) + (60847217286311/1000000000000 : ℝ)*(sp6) + (2870410408224861/100000000000000 : ℝ)*(sp7) + (2870410408224861/100000000000000 : ℝ)*(f.failure) + (6084747723020273/100000000000000 : ℝ)*(f.sum) + (93102998235001/17585000000000000000000000000 : ℝ)*base66 + (22243754588499973191/1758500000000000000000000000000000 : ℝ)*base68 + (1858799978507526809/1758500000000000000000000000000000 : ℝ)*base69 + (27023639046975973191/1758500000000000000000000000000000 : ℝ)*base72 + (53815005802129/17585000000000000000000000000 : ℝ)*base73 + (17611123747689973191/1758500000000000000000000000000000 : ℝ)*base76 + (4976542719634473191/1758500000000000000000000000000000 : ℝ)*base78 + (7282410332098026809/1758500000000000000000000000000000 : ℝ)*base79 + (75260818331739/17585000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (22177841/2000000000000000000000 : ℝ)*base89 + (22177841/2000000000000000000000 : ℝ)*base91 + (22177841/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1374_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31198181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14733/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (701/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5611/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14727/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1374_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1374_s7_0 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-504161999/2500000000 : ℝ)*x 0 + (4227359/7812500 : ℝ)*x 1 + (5245573711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (504161999/2500000000 : ℝ)^2167 ≤ (12288718648063/100000000000000 : ℝ)^1655 := by
    have hnat : (504161999 : ℕ)^2167*100000000000000^1655 ≤ 12288718648063^1655*2500000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504161999 2500000000 12288718648063 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4227359/7812500 : ℝ)^2167 ≤ (22373547218569/50000000000000 : ℝ)^1655 := by
    have hnat : (4227359 : ℕ)^2167*50000000000000^1655 ≤ 22373547218569^1655*7812500^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227359 7812500 22373547218569 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245573711/10000000000 : ℝ)^2167 ≤ (42964186899303/100000000000000 : ℝ)^1655 := by
    have hnat : (5245573711 : ℕ)^2167*100000000000000^1655 ≤ 42964186899303^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245573711 10000000000 42964186899303 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-504161999/2500000000 : ℝ), (4227359/7812500 : ℝ), (5245573711/10000000000 : ℝ)] ![(12288718648063/100000000000000 : ℝ), (22373547218569/50000000000000 : ℝ), (42964186899303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-504161999/2500000000 : ℝ)|^2167 ≤ (12288718648063/100000000000000 : ℝ)^1655
        have hw : |(-504161999/2500000000 : ℝ)|=(504161999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4227359/7812500 : ℝ)|^2167 ≤ (22373547218569/50000000000000 : ℝ)^1655
        have hw : |(4227359/7812500 : ℝ)|=(4227359/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245573711/10000000000 : ℝ)|^2167 ≤ (42964186899303/100000000000000 : ℝ)^1655
        have hw : |(5245573711/10000000000 : ℝ)|=(5245573711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s7_1 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1337103321/2500000000 : ℝ)*x 0 + (-131307397/625000000 : ℝ)*x 1 + (2622786869/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337103321/2500000000 : ℝ)^2167 ≤ (5508801635457/12500000000000 : ℝ)^1655 := by
    have hnat : (1337103321 : ℕ)^2167*12500000000000^1655 ≤ 5508801635457^1655*2500000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337103321 2500000000 5508801635457 12500000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131307397/625000000 : ℝ)^2167 ≤ (6482699858143/50000000000000 : ℝ)^1655 := by
    have hnat : (131307397 : ℕ)^2167*50000000000000^1655 ≤ 6482699858143^1655*625000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131307397 625000000 6482699858143 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622786869/5000000000 : ℝ)^2167 ≤ (42964187188863/100000000000000 : ℝ)^1655 := by
    have hnat : (2622786869 : ℕ)^2167*100000000000000^1655 ≤ 42964187188863^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622786869 5000000000 42964187188863 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337103321/2500000000 : ℝ), (-131307397/625000000 : ℝ), (2622786869/5000000000 : ℝ)] ![(5508801635457/12500000000000 : ℝ), (6482699858143/50000000000000 : ℝ), (42964187188863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337103321/2500000000 : ℝ)|^2167 ≤ (5508801635457/12500000000000 : ℝ)^1655
        have hw : |(1337103321/2500000000 : ℝ)|=(1337103321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-131307397/625000000 : ℝ)|^2167 ≤ (6482699858143/50000000000000 : ℝ)^1655
        have hw : |(-131307397/625000000 : ℝ)|=(131307397/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622786869/5000000000 : ℝ)|^2167 ≤ (42964187188863/100000000000000 : ℝ)^1655
        have hw : |(2622786869/5000000000 : ℝ)|=(2622786869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s7_2 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1337103287/2500000000 : ℝ)*x 0 + (2622786963/5000000000 : ℝ)*x 1 + (-525229571/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337103287/2500000000 : ℝ)^2167 ≤ (22035205808173/50000000000000 : ℝ)^1655 := by
    have hnat : (1337103287 : ℕ)^2167*50000000000000^1655 ≤ 22035205808173^1655*2500000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337103287 2500000000 22035205808173 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622786963/5000000000 : ℝ)^2167 ≤ (42964189205057/100000000000000 : ℝ)^1655 := by
    have hnat : (2622786963 : ℕ)^2167*100000000000000^1655 ≤ 42964189205057^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622786963 5000000000 42964189205057 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (525229571/2500000000 : ℝ)^2167 ≤ (12965399166813/100000000000000 : ℝ)^1655 := by
    have hnat : (525229571 : ℕ)^2167*100000000000000^1655 ≤ 12965399166813^1655*2500000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525229571 2500000000 12965399166813 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337103287/2500000000 : ℝ), (2622786963/5000000000 : ℝ), (-525229571/2500000000 : ℝ)] ![(22035205808173/50000000000000 : ℝ), (42964189205057/100000000000000 : ℝ), (12965399166813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337103287/2500000000 : ℝ)|^2167 ≤ (22035205808173/50000000000000 : ℝ)^1655
        have hw : |(1337103287/2500000000 : ℝ)|=(1337103287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622786963/5000000000 : ℝ)|^2167 ≤ (42964189205057/100000000000000 : ℝ)^1655
        have hw : |(2622786963/5000000000 : ℝ)|=(2622786963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-525229571/2500000000 : ℝ)|^2167 ≤ (12965399166813/100000000000000 : ℝ)^1655
        have hw : |(-525229571/2500000000 : ℝ)|=(525229571/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s7_3 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (431832321/1000000000 : ℝ)*x 0 + (1036561669/2500000000 : ℝ)*x 1 + (4496961167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431832321/1000000000 : ℝ)^2167 ≤ (666076644981/2000000000000 : ℝ)^1655 := by
    have hnat : (431832321 : ℕ)^2167*2000000000000^1655 ≤ 666076644981^1655*1000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431832321 1000000000 666076644981 2000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036561669/2500000000 : ℝ)^2167 ≤ (31576995405459/100000000000000 : ℝ)^1655 := by
    have hnat : (1036561669 : ℕ)^2167*100000000000000^1655 ≤ 31576995405459^1655*2500000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036561669 2500000000 31576995405459 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4496961167/10000000000 : ℝ)^2167 ≤ (35119172335503/100000000000000 : ℝ)^1655 := by
    have hnat : (4496961167 : ℕ)^2167*100000000000000^1655 ≤ 35119172335503^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496961167 10000000000 35119172335503 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(431832321/1000000000 : ℝ), (1036561669/2500000000 : ℝ), (4496961167/10000000000 : ℝ)] ![(666076644981/2000000000000 : ℝ), (31576995405459/100000000000000 : ℝ), (35119172335503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(431832321/1000000000 : ℝ)|^2167 ≤ (666076644981/2000000000000 : ℝ)^1655
        have hw : |(431832321/1000000000 : ℝ)|=(431832321/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036561669/2500000000 : ℝ)|^2167 ≤ (31576995405459/100000000000000 : ℝ)^1655
        have hw : |(1036561669/2500000000 : ℝ)|=(1036561669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4496961167/10000000000 : ℝ)|^2167 ≤ (35119172335503/100000000000000 : ℝ)^1655
        have hw : |(4496961167/10000000000 : ℝ)|=(4496961167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s7_4 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-100832989/500000000 : ℝ)*x 0 + (2623083733/5000000000 : ℝ)*x 1 + (2705211369/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (100832989/500000000 : ℝ)^2167 ≤ (3072203167573/25000000000000 : ℝ)^1655 := by
    have hnat : (100832989 : ℕ)^2167*25000000000000^1655 ≤ 3072203167573^1655*500000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100832989 500000000 3072203167573 25000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623083733/5000000000 : ℝ)^2167 ≤ (8594110939817/20000000000000 : ℝ)^1655 := by
    have hnat : (2623083733 : ℕ)^2167*20000000000000^1655 ≤ 8594110939817^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623083733 5000000000 8594110939817 20000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705211369/5000000000 : ℝ)^2167 ≤ (44740632615603/100000000000000 : ℝ)^1655 := by
    have hnat : (2705211369 : ℕ)^2167*100000000000000^1655 ≤ 44740632615603^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705211369 5000000000 44740632615603 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-100832989/500000000 : ℝ), (2623083733/5000000000 : ℝ), (2705211369/5000000000 : ℝ)] ![(3072203167573/25000000000000 : ℝ), (8594110939817/20000000000000 : ℝ), (44740632615603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-100832989/500000000 : ℝ)|^2167 ≤ (3072203167573/25000000000000 : ℝ)^1655
        have hw : |(-100832989/500000000 : ℝ)|=(100832989/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623083733/5000000000 : ℝ)|^2167 ≤ (8594110939817/20000000000000 : ℝ)^1655
        have hw : |(2623083733/5000000000 : ℝ)|=(2623083733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705211369/5000000000 : ℝ)|^2167 ≤ (44740632615603/100000000000000 : ℝ)^1655
        have hw : |(2705211369/5000000000 : ℝ)|=(2705211369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s7_5 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652822601/5000000000 : ℝ)*x 0 + (-38721387/200000000 : ℝ)*x 1 + (1082084557/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652822601/5000000000 : ℝ)^2167 ≤ (43609558042717/100000000000000 : ℝ)^1655 := by
    have hnat : (2652822601 : ℕ)^2167*100000000000000^1655 ≤ 43609558042717^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652822601 5000000000 43609558042717 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (38721387/200000000 : ℝ)^2167 ≤ (2329961763741/20000000000000 : ℝ)^1655 := by
    have hnat : (38721387 : ℕ)^2167*20000000000000^1655 ≤ 2329961763741^1655*200000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38721387 200000000 2329961763741 20000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082084557/2000000000 : ℝ)^2167 ≤ (44740633124499/100000000000000 : ℝ)^1655 := by
    have hnat : (1082084557 : ℕ)^2167*100000000000000^1655 ≤ 44740633124499^1655*2000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082084557 2000000000 44740633124499 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652822601/5000000000 : ℝ), (-38721387/200000000 : ℝ), (1082084557/2000000000 : ℝ)] ![(43609558042717/100000000000000 : ℝ), (2329961763741/20000000000000 : ℝ), (44740633124499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652822601/5000000000 : ℝ)|^2167 ≤ (43609558042717/100000000000000 : ℝ)^1655
        have hw : |(2652822601/5000000000 : ℝ)|=(2652822601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-38721387/200000000 : ℝ)|^2167 ≤ (2329961763741/20000000000000 : ℝ)^1655
        have hw : |(-38721387/200000000 : ℝ)|=(38721387/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082084557/2000000000 : ℝ)|^2167 ≤ (44740633124499/100000000000000 : ℝ)^1655
        have hw : |(1082084557/2000000000 : ℝ)|=(1082084557/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s7_6 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305645267/10000000000 : ℝ)*x 0 + (2705211337/5000000000 : ℝ)*x 1 + (-387213883/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305645267/10000000000 : ℝ)^2167 ≤ (8721911748453/20000000000000 : ℝ)^1655 := by
    have hnat : (5305645267 : ℕ)^2167*20000000000000^1655 ≤ 8721911748453^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305645267 10000000000 8721911748453 20000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705211337/5000000000 : ℝ)^2167 ≤ (44740631922637/100000000000000 : ℝ)^1655 := by
    have hnat : (2705211337 : ℕ)^2167*100000000000000^1655 ≤ 44740631922637^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705211337 5000000000 44740631922637 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (387213883/2000000000 : ℝ)^2167 ≤ (5824904665413/50000000000000 : ℝ)^1655 := by
    have hnat : (387213883 : ℕ)^2167*50000000000000^1655 ≤ 5824904665413^1655*2000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387213883 2000000000 5824904665413 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305645267/10000000000 : ℝ), (2705211337/5000000000 : ℝ), (-387213883/2000000000 : ℝ)] ![(8721911748453/20000000000000 : ℝ), (44740631922637/100000000000000 : ℝ), (5824904665413/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305645267/10000000000 : ℝ)|^2167 ≤ (8721911748453/20000000000000 : ℝ)^1655
        have hw : |(5305645267/10000000000 : ℝ)|=(5305645267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705211337/5000000000 : ℝ)|^2167 ≤ (44740631922637/100000000000000 : ℝ)^1655
        have hw : |(2705211337/5000000000 : ℝ)|=(2705211337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-387213883/2000000000 : ℝ)|^2167 ≤ (5824904665413/50000000000000 : ℝ)^1655
        have hw : |(-387213883/2000000000 : ℝ)|=(387213883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s7_7 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4318348391/10000000000 : ℝ)*x 0 + (89914057/200000000 : ℝ)*x 1 + (2073755693/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4318348391/10000000000 : ℝ)^2167 ≤ (16652043264859/50000000000000 : ℝ)^1655 := by
    have hnat : (4318348391 : ℕ)^2167*50000000000000^1655 ≤ 16652043264859^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4318348391 10000000000 16652043264859 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89914057/200000000 : ℝ)^2167 ≤ (1404252237107/4000000000000 : ℝ)^1655 := by
    have hnat : (89914057 : ℕ)^2167*4000000000000^1655 ≤ 1404252237107^1655*200000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89914057 200000000 1404252237107 4000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2073755693/5000000000 : ℝ)^2167 ≤ (3158960752337/10000000000000 : ℝ)^1655 := by
    have hnat : (2073755693 : ℕ)^2167*10000000000000^1655 ≤ 3158960752337^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073755693 5000000000 3158960752337 10000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4318348391/10000000000 : ℝ), (89914057/200000000 : ℝ), (2073755693/5000000000 : ℝ)] ![(16652043264859/50000000000000 : ℝ), (1404252237107/4000000000000 : ℝ), (3158960752337/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4318348391/10000000000 : ℝ)|^2167 ≤ (16652043264859/50000000000000 : ℝ)^1655
        have hw : |(4318348391/10000000000 : ℝ)|=(4318348391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(89914057/200000000 : ℝ)|^2167 ≤ (1404252237107/4000000000000 : ℝ)^1655
        have hw : |(89914057/200000000 : ℝ)|=(89914057/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2073755693/5000000000 : ℝ)|^2167 ≤ (3158960752337/10000000000000 : ℝ)^1655
        have hw : |(2073755693/5000000000 : ℝ)|=(2073755693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1374_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31198181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14727/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5611/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11223/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7363/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14727/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5611/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14727/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5611/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14727/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5611/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14727/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5611/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14727/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5611/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14727/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5611/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5611/50000 : ℝ) ^ (4333/1024 : ℝ) ≤ (382370399044861/4000000000000000000 : ℝ) := by
    have hpowers : (5611/50000 : ℝ)^4333 ≤ (382370399044861/4000000000000000000 : ℝ)^1024 := by
      have hnat : (5611 : ℕ)^4333*4000000000000000000^1024 ≤ 382370399044861^1024*50000^4333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5611 50000 382370399044861 4000000000000000000 4333 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5611/50000 : ℝ)) (X := (382370399044861/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14727/100000 : ℝ) ^ (4333/1024 : ℝ) ≤ (30194031126991111/100000000000000000000 : ℝ) := by
    have hpowers : (14727/100000 : ℝ)^4333 ≤ (30194031126991111/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14727 : ℕ)^4333*100000000000000000000^1024 ≤ 30194031126991111^1024*100000^4333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14727 100000 30194031126991111 100000000000000000000 4333 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14727/100000 : ℝ)) (X := (30194031126991111/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000382370399044861/2000000000000000000 : ℝ) ≤ (10000451787108537/10000000000000000 : ℝ) ^ (4333/1024 : ℝ) := by
    have hpowers : (2000382370399044861/2000000000000000000 : ℝ)^1024 ≤ (10000451787108537/10000000000000000 : ℝ)^4333 := by
      have hnat : (2000382370399044861 : ℕ)^1024*10000000000000000^4333 ≤ 10000451787108537^4333*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000382370399044861 2000000000000000000 10000451787108537 10000000000000000 1024 4333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000451787108537/10000000000000000 : ℝ)) (X := (2000382370399044861/2000000000000000000 : ℝ)) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25009938322775778159/25000000000000000000 : ℝ) ≤ (10000939330543449/10000000000000000 : ℝ) ^ (4333/1024 : ℝ) := by
    have hpowers : (25009938322775778159/25000000000000000000 : ℝ)^1024 ≤ (10000939330543449/10000000000000000 : ℝ)^4333 := by
      have hnat : (25009938322775778159 : ℕ)^1024*10000000000000000^4333 ≤ 10000939330543449^4333*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009938322775778159 25000000000000000000 10000939330543449 10000000000000000 1024 4333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000939330543449/10000000000000000 : ℝ)) (X := (25009938322775778159/25000000000000000000 : ℝ)) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030194031126991111/50000000000000000000 : ℝ) ≤ (10001426873978361/10000000000000000 : ℝ) ^ (4333/1024 : ℝ) := by
    have hpowers : (50030194031126991111/50000000000000000000 : ℝ)^1024 ≤ (10001426873978361/10000000000000000 : ℝ)^4333 := by
      have hnat : (50030194031126991111 : ℕ)^1024*10000000000000000^4333 ≤ 10001426873978361^4333*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030194031126991111 50000000000000000000 10001426873978361 10000000000000000 1024 4333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001426873978361/10000000000000000 : ℝ)) (X := (50030194031126991111/50000000000000000000 : ℝ)) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(382370399044861/4000000000000000000 : ℝ) ≤ ((35040641088962257257/35050000000000000000 : ℝ)+2*(15235732341/10953125000000 : ℝ)*(5611/50000 : ℝ))^(4333/1024 : ℝ) := by
    rw [show (35040641088962257257/35050000000000000000 : ℝ)+2*(15235732341/10953125000000 : ℝ)*(5611/50000 : ℝ)=(10000451787108537/10000000000000000 : ℝ) by norm_num, show 1+2*(382370399044861/4000000000000000000 : ℝ)=(2000382370399044861/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30194031126991111/100000000000000000000 : ℝ)+(382370399044861/4000000000000000000 : ℝ) ≤ ((35040641088962257257/35050000000000000000 : ℝ)+(15235732341/10953125000000 : ℝ)*((14727/100000 : ℝ)+(5611/50000 : ℝ)))^(4333/1024 : ℝ) := by
    rw [show (35040641088962257257/35050000000000000000 : ℝ)+(15235732341/10953125000000 : ℝ)*((14727/100000 : ℝ)+(5611/50000 : ℝ))=(10000939330543449/10000000000000000 : ℝ) by norm_num, show 1+(30194031126991111/100000000000000000000 : ℝ)+(382370399044861/4000000000000000000 : ℝ)=(25009938322775778159/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30194031126991111/100000000000000000000 : ℝ) ≤ ((35040641088962257257/35050000000000000000 : ℝ)+2*(15235732341/10953125000000 : ℝ)*(14727/100000 : ℝ))^(4333/1024 : ℝ) := by
    rw [show (35040641088962257257/35050000000000000000 : ℝ)+2*(15235732341/10953125000000 : ℝ)*(14727/100000 : ℝ)=(10001426873978361/10000000000000000 : ℝ) by norm_num, show 1+2*(30194031126991111/100000000000000000000 : ℝ)=(50030194031126991111/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35040641088962257257/35050000000000000000 : ℝ)*(X 1 0+X 2 0)+(15235732341/10953125000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4333/1024 : ℝ)) (lo := (5611/50000 : ℝ)) (hi := (14727/100000 : ℝ)) (c := (35040641088962257257/35050000000000000000 : ℝ)) (alpha := (15235732341/10953125000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35040641088962257257/35050000000000000000 : ℝ)*(X 0 1+X 2 1)+(15235732341/10953125000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4333/1024 : ℝ)) (lo := (5611/50000 : ℝ)) (hi := (14727/100000 : ℝ)) (c := (35040641088962257257/35050000000000000000 : ℝ)) (alpha := (15235732341/10953125000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35040641088962257257/35050000000000000000 : ℝ)*(X 0 2+X 1 2)+(15235732341/10953125000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4333/1024 : ℝ)) (lo := (5611/50000 : ℝ)) (hi := (14727/100000 : ℝ)) (c := (35040641088962257257/35050000000000000000 : ℝ)) (alpha := (15235732341/10953125000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-504161999/2500000000 : ℝ)*X 0 0+(4227359/7812500 : ℝ)*X 0 1+(5245573711/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337103321/2500000000 : ℝ)*X 1 0+(-131307397/625000000 : ℝ)*X 1 1+(2622786869/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337103287/2500000000 : ℝ)*X 2 0+(2622786963/5000000000 : ℝ)*X 2 1+(-525229571/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((431832321/1000000000 : ℝ)*X 0 0+(1036561669/2500000000 : ℝ)*X 0 1+(4496961167/10000000000 : ℝ)*X 0 2+(431832321/1000000000 : ℝ)*X 1 0+(1036561669/2500000000 : ℝ)*X 1 1+(4496961167/10000000000 : ℝ)*X 1 2+(431832321/1000000000 : ℝ)*X 2 0+(1036561669/2500000000 : ℝ)*X 2 1+(4496961167/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-100832989/500000000 : ℝ)*X 0 0+(2623083733/5000000000 : ℝ)*X 0 1+(2705211369/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652822601/5000000000 : ℝ)*X 1 0+(-38721387/200000000 : ℝ)*X 1 1+(1082084557/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305645267/10000000000 : ℝ)*X 2 0+(2705211337/5000000000 : ℝ)*X 2 1+(-387213883/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4318348391/10000000000 : ℝ)*X 0 0+(89914057/200000000 : ℝ)*X 0 1+(2073755693/5000000000 : ℝ)*X 0 2+(4318348391/10000000000 : ℝ)*X 1 0+(89914057/200000000 : ℝ)*X 1 1+(2073755693/5000000000 : ℝ)*X 1 2+(4318348391/10000000000 : ℝ)*X 2 0+(89914057/200000000 : ℝ)*X 2 1+(2073755693/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1299339165700120651529670201/219062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1215746201/100000000000000 : ℝ)*(base19) + (206077143/20000000000000 : ℝ)*(base23) + (13704269/12500000000000 : ℝ)*(upper3) + (16935533/100000000000000 : ℝ)*(upper4) + (1812507/1250000000000 : ℝ)*(upper5) + (1111959837809331/25000000000000 : ℝ)*(major0) + (1111959837809331/25000000000000 : ℝ)*(major1) + (177913574049493/4000000000000 : ℝ)*(major2) + (6044303793519861/100000000000000 : ℝ)*(sp0) + (6044331980623313/100000000000000 : ℝ)*(sp1) + (30221660829919/500000000000 : ℝ)*(sp2) + (35641677094017/1250000000000 : ℝ)*(sp3) + (29402849653/100000000000000 : ℝ)*(sp4) + (11140871669/100000000000000 : ℝ)*(sp7) + (712836327098257/25000000000000 : ℝ)*(f.failure) + (3022166598184757/50000000000000 : ℝ)*(f.sum) + (27328599061631/17525000000000000000000000000 : ℝ)*base66 + (14946282302537934933/876250000000000000000000000000000 : ℝ)*base68 + (1313629236609427299/140200000000000000000000000000000 : ℝ)*base70 + (25653056662716684933/876250000000000000000000000000000 : ℝ)*base72 + (3621304141047/8762500000000000000000000000 : ℝ)*base73 + (657755222148772701/140200000000000000000000000000000 : ℝ)*base75 + (13770775833724484933/876250000000000000000000000000000 : ℝ)*base78 + (15643455476138234933/876250000000000000000000000000000 : ℝ)*base80 + (33756412459181/8762500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (6670517/500000000000000000000 : ℝ)*base89 + (6670517/500000000000000000000 : ℝ)*base91 + (1670517/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21155806690225477782231/3505000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22723227/2000000000000 : ℝ)*(base19) + (129456887/10000000000000 : ℝ)*(base23) + (200300179/50000000000000 : ℝ)*(lower1) + (29892709/20000000000000 : ℝ)*(upper3) + (2569247/6250000000000 : ℝ)*(lower4) + (109200733/100000000000000 : ℝ)*(upper5) + (896003061029801/20000000000000 : ℝ)*(major0) + (896003061029801/20000000000000 : ℝ)*(major1) + (896003061029801/20000000000000 : ℝ)*(major2) + (786827447/100000000000000 : ℝ)*(sp2) + (1217611657331393/20000000000000 : ℝ)*(sp4) + (1217611430099123/20000000000000 : ℝ)*(sp5) + (6088056205260647/100000000000000 : ℝ)*(sp6) + (1435986061222289/50000000000000 : ℝ)*(sp7) + (1435986061222289/50000000000000 : ℝ)*(f.failure) + (1217611657331393/20000000000000 : ℝ)*(f.sum) + (3871655369011/1752500000000000000000000000 : ℝ)*base65 + (22966528168166715857/701000000000000000000000000000000 : ℝ)*base67 + (2164943820721284143/701000000000000000000000000000000 : ℝ)*base70 + (40812645586328715857/701000000000000000000000000000000 : ℝ)*base71 + (3751966298869/1752500000000000000000000000 : ℝ)*base74 + (30083497338173715857/701000000000000000000000000000000 : ℝ)*base75 + (3597240777846284143/701000000000000000000000000000000 : ℝ)*base78 + (5892069005143284143/701000000000000000000000000000000 : ℝ)*base80 + (14945277543263/3505000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (3456309/1000000000000000000000 : ℝ)*base89 + (3456309/1000000000000000000000 : ℝ)*base91 + (3456309/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1374_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31198181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14727/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5611/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11223/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7363/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1374_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1374_box_0 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-185189119/1000000000 : ℝ)*x 0 + (269429823/500000000 : ℝ)*x 1 + (5388596251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (185189119/1000000000 : ℝ)^2167 ≤ (2198218762913/20000000000000 : ℝ)^1655 := by
    have hnat : (185189119 : ℕ)^2167*20000000000000^1655 ≤ 2198218762913^1655*1000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      185189119 1000000000 2198218762913 20000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269429823/500000000 : ℝ)^2167 ≤ (8900890843093/20000000000000 : ℝ)^1655 := by
    have hnat : (269429823 : ℕ)^2167*20000000000000^1655 ≤ 8900890843093^1655*500000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269429823 500000000 8900890843093 20000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5388596251/10000000000 : ℝ)^2167 ≤ (22252225977663/50000000000000 : ℝ)^1655 := by
    have hnat : (5388596251 : ℕ)^2167*50000000000000^1655 ≤ 22252225977663^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388596251 10000000000 22252225977663 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-185189119/1000000000 : ℝ), (269429823/500000000 : ℝ), (5388596251/10000000000 : ℝ)] ![(2198218762913/20000000000000 : ℝ), (8900890843093/20000000000000 : ℝ), (22252225977663/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-185189119/1000000000 : ℝ)|^2167 ≤ (2198218762913/20000000000000 : ℝ)^1655
        have hw : |(-185189119/1000000000 : ℝ)|=(185189119/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269429823/500000000 : ℝ)|^2167 ≤ (8900890843093/20000000000000 : ℝ)^1655
        have hw : |(269429823/500000000 : ℝ)|=(269429823/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5388596251/10000000000 : ℝ)|^2167 ≤ (22252225977663/50000000000000 : ℝ)^1655
        have hw : |(5388596251/10000000000 : ℝ)|=(5388596251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_box_1 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (660695391/1250000000 : ℝ)*x 0 + (-996601213/5000000000 : ℝ)*x 1 + (26942983/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660695391/1250000000 : ℝ)^2167 ≤ (4339355573569/10000000000000 : ℝ)^1655 := by
    have hnat : (660695391 : ℕ)^2167*10000000000000^1655 ≤ 4339355573569^1655*1250000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660695391 1250000000 4339355573569 10000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (996601213/5000000000 : ℝ)^2167 ≤ (12101988521081/100000000000000 : ℝ)^1655 := by
    have hnat : (996601213 : ℕ)^2167*100000000000000^1655 ≤ 12101988521081^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      996601213 5000000000 12101988521081 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26942983/50000000 : ℝ)^2167 ≤ (44504455729433/100000000000000 : ℝ)^1655 := by
    have hnat : (26942983 : ℕ)^2167*100000000000000^1655 ≤ 44504455729433^1655*50000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26942983 50000000 44504455729433 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660695391/1250000000 : ℝ), (-996601213/5000000000 : ℝ), (26942983/50000000 : ℝ)] ![(4339355573569/10000000000000 : ℝ), (12101988521081/100000000000000 : ℝ), (44504455729433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660695391/1250000000 : ℝ)|^2167 ≤ (4339355573569/10000000000000 : ℝ)^1655
        have hw : |(660695391/1250000000 : ℝ)|=(660695391/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-996601213/5000000000 : ℝ)|^2167 ≤ (12101988521081/100000000000000 : ℝ)^1655
        have hw : |(-996601213/5000000000 : ℝ)|=(996601213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(26942983/50000000 : ℝ)|^2167 ≤ (44504455729433/100000000000000 : ℝ)^1655
        have hw : |(26942983/50000000 : ℝ)|=(26942983/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_box_2 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1057112501/2000000000 : ℝ)*x 0 + (336787309/625000000 : ℝ)*x 1 + (-4983007/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057112501/2000000000 : ℝ)^2167 ≤ (43393549038649/100000000000000 : ℝ)^1655 := by
    have hnat : (1057112501 : ℕ)^2167*100000000000000^1655 ≤ 43393549038649^1655*2000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057112501 2000000000 43393549038649 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336787309/625000000 : ℝ)^2167 ≤ (44504459449469/100000000000000 : ℝ)^1655 := by
    have hnat : (336787309 : ℕ)^2167*100000000000000^1655 ≤ 44504459449469^1655*625000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336787309 625000000 44504459449469 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4983007/25000000 : ℝ)^2167 ≤ (19363186391/160000000000 : ℝ)^1655 := by
    have hnat : (4983007 : ℕ)^2167*160000000000^1655 ≤ 19363186391^1655*25000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4983007 25000000 19363186391 160000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057112501/2000000000 : ℝ), (336787309/625000000 : ℝ), (-4983007/25000000 : ℝ)] ![(43393549038649/100000000000000 : ℝ), (44504459449469/100000000000000 : ℝ), (19363186391/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057112501/2000000000 : ℝ)|^2167 ≤ (43393549038649/100000000000000 : ℝ)^1655
        have hw : |(1057112501/2000000000 : ℝ)|=(1057112501/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(336787309/625000000 : ℝ)|^2167 ≤ (44504459449469/100000000000000 : ℝ)^1655
        have hw : |(336787309/625000000 : ℝ)|=(336787309/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4983007/25000000 : ℝ)|^2167 ≤ (19363186391/160000000000 : ℝ)^1655
        have hw : |(-4983007/25000000 : ℝ)|=(4983007/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_box_3 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (178631269/400000000 : ℝ)*x 0 + (2124206827/5000000000 : ℝ)*x 1 + (531051789/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (178631269/400000000 : ℝ)^2167 ≤ (543760755277/1562500000000 : ℝ)^1655 := by
    have hnat : (178631269 : ℕ)^2167*1562500000000^1655 ≤ 543760755277^1655*400000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      178631269 400000000 543760755277 1562500000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2124206827/5000000000 : ℝ)^2167 ≤ (32599652516089/100000000000000 : ℝ)^1655 := by
    have hnat : (2124206827 : ℕ)^2167*100000000000000^1655 ≤ 32599652516089^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124206827 5000000000 32599652516089 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (531051789/1250000000 : ℝ)^2167 ≤ (16299829563589/50000000000000 : ℝ)^1655 := by
    have hnat : (531051789 : ℕ)^2167*50000000000000^1655 ≤ 16299829563589^1655*1250000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531051789 1250000000 16299829563589 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(178631269/400000000 : ℝ), (2124206827/5000000000 : ℝ), (531051789/1250000000 : ℝ)] ![(543760755277/1562500000000 : ℝ), (32599652516089/100000000000000 : ℝ), (16299829563589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(178631269/400000000 : ℝ)|^2167 ≤ (543760755277/1562500000000 : ℝ)^1655
        have hw : |(178631269/400000000 : ℝ)|=(178631269/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2124206827/5000000000 : ℝ)|^2167 ≤ (32599652516089/100000000000000 : ℝ)^1655
        have hw : |(2124206827/5000000000 : ℝ)|=(2124206827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(531051789/1250000000 : ℝ)|^2167 ≤ (16299829563589/50000000000000 : ℝ)^1655
        have hw : |(531051789/1250000000 : ℝ)|=(531051789/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_box_4 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1092075227/5000000000 : ℝ)*x 0 + (2632794973/5000000000 : ℝ)*x 1 + (1316397649/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092075227/5000000000 : ℝ)^2167 ≤ (13642040306903/100000000000000 : ℝ)^1655 := by
    have hnat : (1092075227 : ℕ)^2167*100000000000000^1655 ≤ 13642040306903^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092075227 5000000000 13642040306903 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632794973/5000000000 : ℝ)^2167 ≤ (10794744087421/25000000000000 : ℝ)^1655 := by
    have hnat : (2632794973 : ℕ)^2167*25000000000000^1655 ≤ 10794744087421^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632794973 5000000000 10794744087421 25000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316397649/2500000000 : ℝ)^2167 ≤ (43178983328787/100000000000000 : ℝ)^1655 := by
    have hnat : (1316397649 : ℕ)^2167*100000000000000^1655 ≤ 43178983328787^1655*2500000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316397649 2500000000 43178983328787 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1092075227/5000000000 : ℝ), (2632794973/5000000000 : ℝ), (1316397649/2500000000 : ℝ)] ![(13642040306903/100000000000000 : ℝ), (10794744087421/25000000000000 : ℝ), (43178983328787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1092075227/5000000000 : ℝ)|^2167 ≤ (13642040306903/100000000000000 : ℝ)^1655
        have hw : |(-1092075227/5000000000 : ℝ)|=(1092075227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632794973/5000000000 : ℝ)|^2167 ≤ (10794744087421/25000000000000 : ℝ)^1655
        have hw : |(2632794973/5000000000 : ℝ)|=(2632794973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316397649/2500000000 : ℝ)|^2167 ≤ (43178983328787/100000000000000 : ℝ)^1655
        have hw : |(1316397649/2500000000 : ℝ)|=(1316397649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_box_5 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (671480563/1250000000 : ℝ)*x 0 + (-6383687/31250000 : ℝ)*x 1 + (1053118043/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671480563/1250000000 : ℝ)^2167 ≤ (11080846188113/25000000000000 : ℝ)^1655 := by
    have hnat : (671480563 : ℕ)^2167*25000000000000^1655 ≤ 11080846188113^1655*1250000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671480563 1250000000 11080846188113 25000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6383687/31250000 : ℝ)^2167 ≤ (12497636002801/100000000000000 : ℝ)^1655 := by
    have hnat : (6383687 : ℕ)^2167*100000000000000^1655 ≤ 12497636002801^1655*31250000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6383687 31250000 12497636002801 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053118043/2000000000 : ℝ)^2167 ≤ (43178979237959/100000000000000 : ℝ)^1655 := by
    have hnat : (1053118043 : ℕ)^2167*100000000000000^1655 ≤ 43178979237959^1655*2000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053118043 2000000000 43178979237959 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671480563/1250000000 : ℝ), (-6383687/31250000 : ℝ), (1053118043/2000000000 : ℝ)] ![(11080846188113/25000000000000 : ℝ), (12497636002801/100000000000000 : ℝ), (43178979237959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671480563/1250000000 : ℝ)|^2167 ≤ (11080846188113/25000000000000 : ℝ)^1655
        have hw : |(671480563/1250000000 : ℝ)|=(671480563/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6383687/31250000 : ℝ)|^2167 ≤ (12497636002801/100000000000000 : ℝ)^1655
        have hw : |(-6383687/31250000 : ℝ)|=(6383687/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053118043/2000000000 : ℝ)|^2167 ≤ (43178979237959/100000000000000 : ℝ)^1655
        have hw : |(1053118043/2000000000 : ℝ)|=(1053118043/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_box_6 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2685922111/5000000000 : ℝ)*x 0 + (5265590091/10000000000 : ℝ)*x 1 + (-1021390193/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685922111/5000000000 : ℝ)^2167 ≤ (1385105678307/3125000000000 : ℝ)^1655 := by
    have hnat : (2685922111 : ℕ)^2167*3125000000000^1655 ≤ 1385105678307^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685922111 5000000000 1385105678307 3125000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265590091/10000000000 : ℝ)^2167 ≤ (43178977906561/100000000000000 : ℝ)^1655 := by
    have hnat : (5265590091 : ℕ)^2167*100000000000000^1655 ≤ 43178977906561^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265590091 10000000000 43178977906561 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1021390193/5000000000 : ℝ)^2167 ≤ (12497640376611/100000000000000 : ℝ)^1655 := by
    have hnat : (1021390193 : ℕ)^2167*100000000000000^1655 ≤ 12497640376611^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021390193 5000000000 12497640376611 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685922111/5000000000 : ℝ), (5265590091/10000000000 : ℝ), (-1021390193/5000000000 : ℝ)] ![(1385105678307/3125000000000 : ℝ), (43178977906561/100000000000000 : ℝ), (12497640376611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685922111/5000000000 : ℝ)|^2167 ≤ (1385105678307/3125000000000 : ℝ)^1655
        have hw : |(2685922111/5000000000 : ℝ)|=(2685922111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265590091/10000000000 : ℝ)|^2167 ≤ (43178977906561/100000000000000 : ℝ)^1655
        have hw : |(5265590091/10000000000 : ℝ)|=(5265590091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1021390193/5000000000 : ℝ)|^2167 ≤ (12497640376611/100000000000000 : ℝ)^1655
        have hw : |(-1021390193/5000000000 : ℝ)|=(1021390193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_box_7 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4169893491/10000000000 : ℝ)*x 0 + (1099076401/2500000000 : ℝ)*x 1 + (4396305507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4169893491/10000000000 : ℝ)^2167 ≤ (31813006104981/100000000000000 : ℝ)^1655 := by
    have hnat : (4169893491 : ℕ)^2167*100000000000000^1655 ≤ 31813006104981^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169893491 10000000000 31813006104981 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1099076401/2500000000 : ℝ)^2167 ≤ (34093497434081/100000000000000 : ℝ)^1655 := by
    have hnat : (1099076401 : ℕ)^2167*100000000000000^1655 ≤ 34093497434081^1655*2500000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099076401 2500000000 34093497434081 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4396305507/10000000000 : ℝ)^2167 ≤ (17046748224563/50000000000000 : ℝ)^1655 := by
    have hnat : (4396305507 : ℕ)^2167*50000000000000^1655 ≤ 17046748224563^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4396305507 10000000000 17046748224563 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4169893491/10000000000 : ℝ), (1099076401/2500000000 : ℝ), (4396305507/10000000000 : ℝ)] ![(31813006104981/100000000000000 : ℝ), (34093497434081/100000000000000 : ℝ), (17046748224563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4169893491/10000000000 : ℝ)|^2167 ≤ (31813006104981/100000000000000 : ℝ)^1655
        have hw : |(4169893491/10000000000 : ℝ)|=(4169893491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1099076401/2500000000 : ℝ)|^2167 ≤ (34093497434081/100000000000000 : ℝ)^1655
        have hw : |(1099076401/2500000000 : ℝ)|=(1099076401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4396305507/10000000000 : ℝ)|^2167 ≤ (17046748224563/50000000000000 : ℝ)^1655
        have hw : |(4396305507/10000000000 : ℝ)|=(4396305507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_box_8 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-66071733/312500000 : ℝ)*x 0 + (5180760709/10000000000 : ℝ)*x 1 + (2701300651/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66071733/312500000 : ℝ)^2167 ≤ (1634199945717/12500000000000 : ℝ)^1655 := by
    have hnat : (66071733 : ℕ)^2167*12500000000000^1655 ≤ 1634199945717^1655*312500000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66071733 312500000 1634199945717 12500000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180760709/10000000000 : ℝ)^2167 ≤ (42270436176713/100000000000000 : ℝ)^1655 := by
    have hnat : (5180760709 : ℕ)^2167*100000000000000^1655 ≤ 42270436176713^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180760709 10000000000 42270436176713 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701300651/5000000000 : ℝ)^2167 ≤ (4465596425067/10000000000000 : ℝ)^1655 := by
    have hnat : (2701300651 : ℕ)^2167*10000000000000^1655 ≤ 4465596425067^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701300651 5000000000 4465596425067 10000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-66071733/312500000 : ℝ), (5180760709/10000000000 : ℝ), (2701300651/5000000000 : ℝ)] ![(1634199945717/12500000000000 : ℝ), (42270436176713/100000000000000 : ℝ), (4465596425067/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-66071733/312500000 : ℝ)|^2167 ≤ (1634199945717/12500000000000 : ℝ)^1655
        have hw : |(-66071733/312500000 : ℝ)|=(66071733/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180760709/10000000000 : ℝ)|^2167 ≤ (42270436176713/100000000000000 : ℝ)^1655
        have hw : |(5180760709/10000000000 : ℝ)|=(5180760709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701300651/5000000000 : ℝ)|^2167 ≤ (4465596425067/10000000000000 : ℝ)^1655
        have hw : |(2701300651/5000000000 : ℝ)|=(2701300651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_box_9 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5275734721/10000000000 : ℝ)*x 0 + (-1987427789/10000000000 : ℝ)*x 1 + (2701300689/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275734721/10000000000 : ℝ)^2167 ≤ (10821983516269/25000000000000 : ℝ)^1655 := by
    have hnat : (5275734721 : ℕ)^2167*25000000000000^1655 ≤ 10821983516269^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275734721 10000000000 10821983516269 25000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1987427789/10000000000 : ℝ)^2167 ≤ (301402520943/2500000000000 : ℝ)^1655 := by
    have hnat : (1987427789 : ℕ)^2167*2500000000000^1655 ≤ 301402520943^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1987427789 10000000000 301402520943 2500000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701300689/5000000000 : ℝ)^2167 ≤ (44655965073199/100000000000000 : ℝ)^1655 := by
    have hnat : (2701300689 : ℕ)^2167*100000000000000^1655 ≤ 44655965073199^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701300689 5000000000 44655965073199 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275734721/10000000000 : ℝ), (-1987427789/10000000000 : ℝ), (2701300689/5000000000 : ℝ)] ![(10821983516269/25000000000000 : ℝ), (301402520943/2500000000000 : ℝ), (44655965073199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275734721/10000000000 : ℝ)|^2167 ≤ (10821983516269/25000000000000 : ℝ)^1655
        have hw : |(5275734721/10000000000 : ℝ)|=(5275734721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1987427789/10000000000 : ℝ)|^2167 ≤ (301402520943/2500000000000 : ℝ)^1655
        have hw : |(-1987427789/10000000000 : ℝ)|=(1987427789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701300689/5000000000 : ℝ)|^2167 ≤ (44655965073199/100000000000000 : ℝ)^1655
        have hw : |(2701300689/5000000000 : ℝ)|=(2701300689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_box_10 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2637867313/5000000000 : ℝ)*x 0 + (675325111/1250000000 : ℝ)*x 1 + (-993714293/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637867313/5000000000 : ℝ)^2167 ≤ (21643966522223/50000000000000 : ℝ)^1655 := by
    have hnat : (2637867313 : ℕ)^2167*50000000000000^1655 ≤ 21643966522223^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637867313 5000000000 21643966522223 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675325111/1250000000 : ℝ)^2167 ≤ (44655959770053/100000000000000 : ℝ)^1655 := by
    have hnat : (675325111 : ℕ)^2167*100000000000000^1655 ≤ 44655959770053^1655*1250000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675325111 1250000000 44655959770053 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (993714293/5000000000 : ℝ)^2167 ≤ (12056107168173/100000000000000 : ℝ)^1655 := by
    have hnat : (993714293 : ℕ)^2167*100000000000000^1655 ≤ 12056107168173^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      993714293 5000000000 12056107168173 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637867313/5000000000 : ℝ), (675325111/1250000000 : ℝ), (-993714293/5000000000 : ℝ)] ![(21643966522223/50000000000000 : ℝ), (44655959770053/100000000000000 : ℝ), (12056107168173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637867313/5000000000 : ℝ)|^2167 ≤ (21643966522223/50000000000000 : ℝ)^1655
        have hw : |(2637867313/5000000000 : ℝ)|=(2637867313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(675325111/1250000000 : ℝ)|^2167 ≤ (44655959770053/100000000000000 : ℝ)^1655
        have hw : |(675325111/1250000000 : ℝ)|=(675325111/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-993714293/5000000000 : ℝ)|^2167 ≤ (12056107168173/100000000000000 : ℝ)^1655
        have hw : |(-993714293/5000000000 : ℝ)|=(993714293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_box_11 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2249456151/5000000000 : ℝ)*x 0 + (4231560777/10000000000 : ℝ)*x 1 + (2115780983/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2249456151/5000000000 : ℝ)^2167 ≤ (8784781268501/25000000000000 : ℝ)^1655 := by
    have hnat : (2249456151 : ℕ)^2167*25000000000000^1655 ≤ 8784781268501^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249456151 5000000000 8784781268501 25000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4231560777/10000000000 : ℝ)^2167 ≤ (8107607872113/25000000000000 : ℝ)^1655 := by
    have hnat : (4231560777 : ℕ)^2167*25000000000000^1655 ≤ 8107607872113^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231560777 10000000000 8107607872113 25000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2115780983/5000000000 : ℝ)^2167 ≤ (32430443419949/100000000000000 : ℝ)^1655 := by
    have hnat : (2115780983 : ℕ)^2167*100000000000000^1655 ≤ 32430443419949^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115780983 5000000000 32430443419949 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2249456151/5000000000 : ℝ), (4231560777/10000000000 : ℝ), (2115780983/5000000000 : ℝ)] ![(8784781268501/25000000000000 : ℝ), (8107607872113/25000000000000 : ℝ), (32430443419949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2249456151/5000000000 : ℝ)|^2167 ≤ (8784781268501/25000000000000 : ℝ)^1655
        have hw : |(2249456151/5000000000 : ℝ)|=(2249456151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4231560777/10000000000 : ℝ)|^2167 ≤ (8107607872113/25000000000000 : ℝ)^1655
        have hw : |(4231560777/10000000000 : ℝ)|=(4231560777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2115780983/5000000000 : ℝ)|^2167 ≤ (32430443419949/100000000000000 : ℝ)^1655
        have hw : |(2115780983/5000000000 : ℝ)|=(2115780983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_box_12 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-961011243/5000000000 : ℝ)*x 0 + (5471290973/10000000000 : ℝ)*x 1 + (5254496687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (961011243/5000000000 : ℝ)^2167 ≤ (1153926112433/10000000000000 : ℝ)^1655 := by
    have hnat : (961011243 : ℕ)^2167*10000000000000^1655 ≤ 1153926112433^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961011243 5000000000 1153926112433 10000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5471290973/10000000000 : ℝ)^2167 ≤ (45400832896169/100000000000000 : ℝ)^1655 := by
    have hnat : (5471290973 : ℕ)^2167*100000000000000^1655 ≤ 45400832896169^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471290973 10000000000 45400832896169 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254496687/10000000000 : ℝ)^2167 ≤ (8611981193147/20000000000000 : ℝ)^1655 := by
    have hnat : (5254496687 : ℕ)^2167*20000000000000^1655 ≤ 8611981193147^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254496687 10000000000 8611981193147 20000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-961011243/5000000000 : ℝ), (5471290973/10000000000 : ℝ), (5254496687/10000000000 : ℝ)] ![(1153926112433/10000000000000 : ℝ), (45400832896169/100000000000000 : ℝ), (8611981193147/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-961011243/5000000000 : ℝ)|^2167 ≤ (1153926112433/10000000000000 : ℝ)^1655
        have hw : |(-961011243/5000000000 : ℝ)|=(961011243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5471290973/10000000000 : ℝ)|^2167 ≤ (45400832896169/100000000000000 : ℝ)^1655
        have hw : |(5471290973/10000000000 : ℝ)|=(5471290973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254496687/10000000000 : ℝ)|^2167 ≤ (8611981193147/20000000000000 : ℝ)^1655
        have hw : |(5254496687/10000000000 : ℝ)|=(5254496687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_box_13 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1344905781/2500000000 : ℝ)*x 0 + (-2047149319/10000000000 : ℝ)*x 1 + (2627248487/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344905781/2500000000 : ℝ)^2167 ≤ (138773253239/312500000000 : ℝ)^1655 := by
    have hnat : (1344905781 : ℕ)^2167*312500000000^1655 ≤ 138773253239^1655*2500000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344905781 2500000000 138773253239 312500000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2047149319/10000000000 : ℝ)^2167 ≤ (12532649901923/100000000000000 : ℝ)^1655 := by
    have hnat : (2047149319 : ℕ)^2167*100000000000000^1655 ≤ 12532649901923^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2047149319 10000000000 12532649901923 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627248487/5000000000 : ℝ)^2167 ≤ (10764977261317/25000000000000 : ℝ)^1655 := by
    have hnat : (2627248487 : ℕ)^2167*25000000000000^1655 ≤ 10764977261317^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627248487 5000000000 10764977261317 25000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344905781/2500000000 : ℝ), (-2047149319/10000000000 : ℝ), (2627248487/5000000000 : ℝ)] ![(138773253239/312500000000 : ℝ), (12532649901923/100000000000000 : ℝ), (10764977261317/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344905781/2500000000 : ℝ)|^2167 ≤ (138773253239/312500000000 : ℝ)^1655
        have hw : |(1344905781/2500000000 : ℝ)|=(1344905781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2047149319/10000000000 : ℝ)|^2167 ≤ (12532649901923/100000000000000 : ℝ)^1655
        have hw : |(-2047149319/10000000000 : ℝ)|=(2047149319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627248487/5000000000 : ℝ)|^2167 ≤ (10764977261317/25000000000000 : ℝ)^1655
        have hw : |(2627248487/5000000000 : ℝ)|=(2627248487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_box_14 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5379622423/10000000000 : ℝ)*x 0 + (5254497839/10000000000 : ℝ)*x 1 + (-1023574553/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5379622423/10000000000 : ℝ)^2167 ≤ (11101858364933/25000000000000 : ℝ)^1655 := by
    have hnat : (5379622423 : ℕ)^2167*25000000000000^1655 ≤ 11101858364933^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379622423 10000000000 11101858364933 25000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5254497839/10000000000 : ℝ)^2167 ≤ (8611983665357/20000000000000 : ℝ)^1655 := by
    have hnat : (5254497839 : ℕ)^2167*20000000000000^1655 ≤ 8611983665357^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254497839 10000000000 8611983665357 20000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1023574553/5000000000 : ℝ)^2167 ≤ (12532648194529/100000000000000 : ℝ)^1655 := by
    have hnat : (1023574553 : ℕ)^2167*100000000000000^1655 ≤ 12532648194529^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023574553 5000000000 12532648194529 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5379622423/10000000000 : ℝ), (5254497839/10000000000 : ℝ), (-1023574553/5000000000 : ℝ)] ![(11101858364933/25000000000000 : ℝ), (8611983665357/20000000000000 : ℝ), (12532648194529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5379622423/10000000000 : ℝ)|^2167 ≤ (11101858364933/25000000000000 : ℝ)^1655
        have hw : |(5379622423/10000000000 : ℝ)|=(5379622423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5254497839/10000000000 : ℝ)|^2167 ≤ (8611983665357/20000000000000 : ℝ)^1655
        have hw : |(5254497839/10000000000 : ℝ)|=(5254497839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1023574553/5000000000 : ℝ)|^2167 ≤ (12532648194529/100000000000000 : ℝ)^1655
        have hw : |(-1023574553/5000000000 : ℝ)|=(1023574553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_box_15 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4142758199/10000000000 : ℝ)*x 0 + (440963377/1000000000 : ℝ)*x 1 + (2204816489/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4142758199/10000000000 : ℝ)^2167 ≤ (31542213296641/100000000000000 : ℝ)^1655 := by
    have hnat : (4142758199 : ℕ)^2167*100000000000000^1655 ≤ 31542213296641^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4142758199 10000000000 31542213296641 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (440963377/1000000000 : ℝ)^2167 ≤ (2139306085627/6250000000000 : ℝ)^1655 := by
    have hnat : (440963377 : ℕ)^2167*6250000000000^1655 ≤ 2139306085627^1655*1000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440963377 1000000000 2139306085627 6250000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2204816489/5000000000 : ℝ)^2167 ≤ (4278611165049/12500000000000 : ℝ)^1655 := by
    have hnat : (2204816489 : ℕ)^2167*12500000000000^1655 ≤ 4278611165049^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2204816489 5000000000 4278611165049 12500000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4142758199/10000000000 : ℝ), (440963377/1000000000 : ℝ), (2204816489/5000000000 : ℝ)] ![(31542213296641/100000000000000 : ℝ), (2139306085627/6250000000000 : ℝ), (4278611165049/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4142758199/10000000000 : ℝ)|^2167 ≤ (31542213296641/100000000000000 : ℝ)^1655
        have hw : |(4142758199/10000000000 : ℝ)|=(4142758199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(440963377/1000000000 : ℝ)|^2167 ≤ (2139306085627/6250000000000 : ℝ)^1655
        have hw : |(440963377/1000000000 : ℝ)|=(440963377/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2204816489/5000000000 : ℝ)|^2167 ≤ (4278611165049/12500000000000 : ℝ)^1655
        have hw : |(2204816489/5000000000 : ℝ)|=(2204816489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1374_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31198181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7363/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11223/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62869/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14751/25000 : ℝ) ∧ (4007/5000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (21119/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7363/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11223/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7363/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11223/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7363/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11223/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7363/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11223/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7363/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11223/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7363/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11223/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11223/100000 : ℝ) ^ (4333/1024 : ℝ) ≤ (9562864976125497/100000000000000000000 : ℝ) := by
    have hpowers : (11223/100000 : ℝ)^4333 ≤ (9562864976125497/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11223 : ℕ)^4333*100000000000000000000^1024 ≤ 9562864976125497^1024*100000^4333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11223 100000 9562864976125497 100000000000000000000 4333 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11223/100000 : ℝ)) (X := (9562864976125497/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7363/50000 : ℝ) ^ (4333/1024 : ℝ) ≤ (30185356558175291/100000000000000000000 : ℝ) := by
    have hpowers : (7363/50000 : ℝ)^4333 ≤ (30185356558175291/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7363 : ℕ)^4333*100000000000000000000^1024 ≤ 30185356558175291^1024*50000^4333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7363 50000 30185356558175291 100000000000000000000 4333 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7363/50000 : ℝ)) (X := (30185356558175291/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009562864976125497/50000000000000000000 : ℝ) ≤ (2500112989368653/2500000000000000 : ℝ) ^ (4333/1024 : ℝ) := by
    have hpowers : (50009562864976125497/50000000000000000000 : ℝ)^1024 ≤ (2500112989368653/2500000000000000 : ℝ)^4333 := by
      have hnat : (50009562864976125497 : ℕ)^1024*2500000000000000^4333 ≤ 2500112989368653^4333*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009562864976125497 50000000000000000000 2500112989368653 2500000000000000 1024 4333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500112989368653/2500000000000000 : ℝ)) (X := (50009562864976125497/50000000000000000000 : ℝ)) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25009937055383575197/25000000000000000000 : ℝ) ≤ (10000939210772779/10000000000000000 : ℝ) ^ (4333/1024 : ℝ) := by
    have hpowers : (25009937055383575197/25000000000000000000 : ℝ)^1024 ≤ (10000939210772779/10000000000000000 : ℝ)^4333 := by
      have hnat : (25009937055383575197 : ℕ)^1024*10000000000000000^4333 ≤ 10000939210772779^4333*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009937055383575197 25000000000000000000 10000939210772779 10000000000000000 1024 4333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000939210772779/10000000000000000 : ℝ)) (X := (25009937055383575197/25000000000000000000 : ℝ)) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030185356558175291/50000000000000000000 : ℝ) ≤ (5000713232035473/5000000000000000 : ℝ) ^ (4333/1024 : ℝ) := by
    have hpowers : (50030185356558175291/50000000000000000000 : ℝ)^1024 ≤ (5000713232035473/5000000000000000 : ℝ)^4333 := by
      have hnat : (50030185356558175291 : ℕ)^1024*5000000000000000^4333 ≤ 5000713232035473^4333*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030185356558175291 50000000000000000000 5000713232035473 5000000000000000 1024 4333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000713232035473/5000000000000000 : ℝ)) (X := (50030185356558175291/50000000000000000000 : ℝ)) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9562864976125497/100000000000000000000 : ℝ) ≤ ((17510323159751454677/17515000000000000000 : ℝ)+2*(487253298167/350300000000000 : ℝ)*(11223/100000 : ℝ))^(4333/1024 : ℝ) := by
    rw [show (17510323159751454677/17515000000000000000 : ℝ)+2*(487253298167/350300000000000 : ℝ)*(11223/100000 : ℝ)=(2500112989368653/2500000000000000 : ℝ) by norm_num, show 1+2*(9562864976125497/100000000000000000000 : ℝ)=(50009562864976125497/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30185356558175291/100000000000000000000 : ℝ)+(9562864976125497/100000000000000000000 : ℝ) ≤ ((17510323159751454677/17515000000000000000 : ℝ)+(487253298167/350300000000000 : ℝ)*((7363/50000 : ℝ)+(11223/100000 : ℝ)))^(4333/1024 : ℝ) := by
    rw [show (17510323159751454677/17515000000000000000 : ℝ)+(487253298167/350300000000000 : ℝ)*((7363/50000 : ℝ)+(11223/100000 : ℝ))=(10000939210772779/10000000000000000 : ℝ) by norm_num, show 1+(30185356558175291/100000000000000000000 : ℝ)+(9562864976125497/100000000000000000000 : ℝ)=(25009937055383575197/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30185356558175291/100000000000000000000 : ℝ) ≤ ((17510323159751454677/17515000000000000000 : ℝ)+2*(487253298167/350300000000000 : ℝ)*(7363/50000 : ℝ))^(4333/1024 : ℝ) := by
    rw [show (17510323159751454677/17515000000000000000 : ℝ)+2*(487253298167/350300000000000 : ℝ)*(7363/50000 : ℝ)=(5000713232035473/5000000000000000 : ℝ) by norm_num, show 1+2*(30185356558175291/100000000000000000000 : ℝ)=(50030185356558175291/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17510323159751454677/17515000000000000000 : ℝ)*(X 1 0+X 2 0)+(487253298167/350300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4333/1024 : ℝ)) (lo := (11223/100000 : ℝ)) (hi := (7363/50000 : ℝ)) (c := (17510323159751454677/17515000000000000000 : ℝ)) (alpha := (487253298167/350300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17510323159751454677/17515000000000000000 : ℝ)*(X 0 1+X 2 1)+(487253298167/350300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4333/1024 : ℝ)) (lo := (11223/100000 : ℝ)) (hi := (7363/50000 : ℝ)) (c := (17510323159751454677/17515000000000000000 : ℝ)) (alpha := (487253298167/350300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17510323159751454677/17515000000000000000 : ℝ)*(X 0 2+X 1 2)+(487253298167/350300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4333/1024 : ℝ)) (lo := (11223/100000 : ℝ)) (hi := (7363/50000 : ℝ)) (c := (17510323159751454677/17515000000000000000 : ℝ)) (alpha := (487253298167/350300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-185189119/1000000000 : ℝ)*X 0 0+(269429823/500000000 : ℝ)*X 0 1+(5388596251/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((660695391/1250000000 : ℝ)*X 1 0+(-996601213/5000000000 : ℝ)*X 1 1+(26942983/50000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1057112501/2000000000 : ℝ)*X 2 0+(336787309/625000000 : ℝ)*X 2 1+(-4983007/25000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((178631269/400000000 : ℝ)*X 0 0+(2124206827/5000000000 : ℝ)*X 0 1+(531051789/1250000000 : ℝ)*X 0 2+(178631269/400000000 : ℝ)*X 1 0+(2124206827/5000000000 : ℝ)*X 1 1+(531051789/1250000000 : ℝ)*X 1 2+(178631269/400000000 : ℝ)*X 2 0+(2124206827/5000000000 : ℝ)*X 2 1+(531051789/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1092075227/5000000000 : ℝ)*X 0 0+(2632794973/5000000000 : ℝ)*X 0 1+(1316397649/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((671480563/1250000000 : ℝ)*X 1 0+(-6383687/31250000 : ℝ)*X 1 1+(1053118043/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2685922111/5000000000 : ℝ)*X 2 0+(5265590091/10000000000 : ℝ)*X 2 1+(-1021390193/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4169893491/10000000000 : ℝ)*X 0 0+(1099076401/2500000000 : ℝ)*X 0 1+(4396305507/10000000000 : ℝ)*X 0 2+(4169893491/10000000000 : ℝ)*X 1 0+(1099076401/2500000000 : ℝ)*X 1 1+(4396305507/10000000000 : ℝ)*X 1 2+(4169893491/10000000000 : ℝ)*X 2 0+(1099076401/2500000000 : ℝ)*X 2 1+(4396305507/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-66071733/312500000 : ℝ)*X 0 0+(5180760709/10000000000 : ℝ)*X 0 1+(2701300651/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5275734721/10000000000 : ℝ)*X 1 0+(-1987427789/10000000000 : ℝ)*X 1 1+(2701300689/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2637867313/5000000000 : ℝ)*X 2 0+(675325111/1250000000 : ℝ)*X 2 1+(-993714293/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2249456151/5000000000 : ℝ)*X 0 0+(4231560777/10000000000 : ℝ)*X 0 1+(2115780983/5000000000 : ℝ)*X 0 2+(2249456151/5000000000 : ℝ)*X 1 0+(4231560777/10000000000 : ℝ)*X 1 1+(2115780983/5000000000 : ℝ)*X 1 2+(2249456151/5000000000 : ℝ)*X 2 0+(4231560777/10000000000 : ℝ)*X 2 1+(2115780983/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-961011243/5000000000 : ℝ)*X 0 0+(5471290973/10000000000 : ℝ)*X 0 1+(5254496687/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1344905781/2500000000 : ℝ)*X 1 0+(-2047149319/10000000000 : ℝ)*X 1 1+(2627248487/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5379622423/10000000000 : ℝ)*X 2 0+(5254497839/10000000000 : ℝ)*X 2 1+(-1023574553/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4142758199/10000000000 : ℝ)*X 0 0+(440963377/1000000000 : ℝ)*X 0 1+(2204816489/5000000000 : ℝ)*X 0 2+(4142758199/10000000000 : ℝ)*X 1 0+(440963377/1000000000 : ℝ)*X 1 1+(2204816489/5000000000 : ℝ)*X 1 2+(4142758199/10000000000 : ℝ)*X 2 0+(440963377/1000000000 : ℝ)*X 2 1+(2204816489/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62869/100000 : ℝ) ≤ (-4301217079298219959603643566419/6841796875000000000000000000000 : ℝ) := by norm_num
    linear_combination (25981293/12500000000000 : ℝ)*(lower0) + (3782197/5000000000000 : ℝ)*(lower3) + (299531311/100000000000000 : ℝ)*(lower4) + (184769032742511/6250000000000 : ℝ)*(major0) + (184769032742511/6250000000000 : ℝ)*(major1) + (184769032742511/6250000000000 : ℝ)*(major2) + (5553530239/100000000000000 : ℝ)*(sp1) + (1353504683/5000000000000 : ℝ)*(sp2) + (504797277001789/12500000000000 : ℝ)*(sp4) + (4038381592287469/100000000000000 : ℝ)*(sp5) + (252397504732753/6250000000000 : ℝ)*(sp6) + (473789817697577/25000000000000 : ℝ)*(sp7) + (2232450849/25000000000000 : ℝ)*(sp12) + (9111487293/50000000000000 : ℝ)*(sp15) + (947588746882447/50000000000000 : ℝ)*(f.failure) + (1009596786454427/25000000000000 : ℝ)*(f.sum) + (7273299156839/8757500000000000000000000000 : ℝ)*base66 + (334179411484726053/109468750000000000000000000000000 : ℝ)*base68 + (735259288755601053/109468750000000000000000000000000 : ℝ)*base70 + (159692474431413553/109468750000000000000000000000000 : ℝ)*base72 + (21881165007611/8757500000000000000000000000 : ℝ)*base73 + (997343265042882303/109468750000000000000000000000000 : ℝ)*base76 + (731373425086538553/109468750000000000000000000000000 : ℝ)*base78 + (138244793167351053/109468750000000000000000000000000 : ℝ)*base80 + (2910466795853/1094687500000000000000000000 : ℝ)*base82 + (7228907/1000000000000000000000 : ℝ)*base89 + (7228907/1000000000000000000000 : ℝ)*base91 + (7228907/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (14751/25000 : ℝ) ≤ (258373506031071194713745630389329/437875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (57062653/100000000000000 : ℝ)*(lower0) + (8506031/12500000000000 : ℝ)*(lower1) + (261191709/100000000000000 : ℝ)*(lower4) + (32825951/100000000000000 : ℝ)*(lower5) + (1513039148016559/50000000000000 : ℝ)*(major0) + (1513039148016559/50000000000000 : ℝ)*(major1) + (1513039148016559/50000000000000 : ℝ)*(major2) + (409257599329771/10000000000000 : ℝ)*(sp0) + (12789279577231/312500000000 : ℝ)*(sp1) + (2046285093053709/50000000000000 : ℝ)*(sp2) + (193990687856649/10000000000000 : ℝ)*(sp3) + (5753623811/50000000000000 : ℝ)*(sp5) + (5392927063/50000000000000 : ℝ)*(sp6) + (4978663833/100000000000000 : ℝ)*(sp12) + (193990687856649/10000000000000 : ℝ)*(f.failure) + (4092580971961543/100000000000000 : ℝ)*(f.sum) + (51299162418987/8757500000000000000000000000 : ℝ)*base66 + (3042597541400103557/875750000000000000000000000000000 : ℝ)*base68 + (5149889187494103557/875750000000000000000000000000000 : ℝ)*base70 + (6178729496278146443/875750000000000000000000000000000 : ℝ)*base71 + (256496780258097/8757500000000000000000000000 : ℝ)*base74 + (1985910756444146443/875750000000000000000000000000000 : ℝ)*base75 + (2178562224082353557/875750000000000000000000000000000 : ℝ)*base78 + (22134832004236853557/875750000000000000000000000000000 : ℝ)*base80 + (28665654748523/8757500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (1555469/200000000000000000000 : ℝ)*base89 + (1555469/200000000000000000000 : ℝ)*base91 + (1555469/200000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (4007/5000 : ℝ) ≤ (175461046067037802773365508840129/218937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (453842681/100000000000000 : ℝ)*(upper0) + (110093899/100000000000000 : ℝ)*(upper2) + (519249537/100000000000000 : ℝ)*(lower5) + (834185742574141/25000000000000 : ℝ)*(major0) + (834185742574141/25000000000000 : ℝ)*(major1) + (834185742574141/25000000000000 : ℝ)*(major2) + (1368902619/2000000000000 : ℝ)*(sp1) + (28777322881/100000000000000 : ℝ)*(sp3) + (2261715401/100000000000000 : ℝ)*(sp4) + (4507705077007851/100000000000000 : ℝ)*(sp8) + (4507640960332237/100000000000000 : ℝ)*(sp9) + (2253854702731593/50000000000000 : ℝ)*(sp10) + (2139033734236087/100000000000000 : ℝ)*(sp11) + (1033369967/50000000000000 : ℝ)*(sp12) + (267382813944871/12500000000000 : ℝ)*(f.failure) + (2253854702731593/50000000000000 : ℝ)*(f.sum) + (83373649676213/17515000000000000000000000000 : ℝ)*base65 + (14382014065028557457/437875000000000000000000000000000 : ℝ)*base67 + (3411015677712692543/437875000000000000000000000000000 : ℝ)*base70 + (424999247822557457/437875000000000000000000000000000 : ℝ)*base71 + (12216540293253/4378750000000000000000000000 : ℝ)*base74 + (4363132360686442543/437875000000000000000000000000000 : ℝ)*base76 + (6090941503525432457/437875000000000000000000000000000 : ℝ)*base77 + (2849346088835682457/437875000000000000000000000000000 : ℝ)*base79 + (2083343479709/8757500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (520349/250000000000000000000 : ℝ)*base90 + (520349/250000000000000000000 : ℝ)*base92 + (520349/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-21119/25000 : ℝ) ≤ (-184944134470699146259376122745403/218937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (42001011/50000000000000 : ℝ)*(lower0) + (17145117/10000000000000 : ℝ)*(upper3) + (398581/50000000000000 : ℝ)*(upper5) + (843412542539487/25000000000000 : ℝ)*(major0) + (843412542539487/25000000000000 : ℝ)*(major1) + (843412542539487/25000000000000 : ℝ)*(major2) + (10993950737/100000000000000 : ℝ)*(sp4) + (415694275879/100000000000000 : ℝ)*(sp5) + (245304362959/100000000000000 : ℝ)*(sp7) + (6918714809/25000000000000 : ℝ)*(sp8) + (2306348573582503/50000000000000 : ℝ)*(sp12) + (46123201216991/1000000000000 : ℝ)*(sp13) + (4612735815974979/100000000000000 : ℝ)*(sp14) + (216247704804467/10000000000000 : ℝ)*(sp15) + (540680588101907/25000000000000 : ℝ)*(f.failure) + (4612735815974979/100000000000000 : ℝ)*(f.sum) + (37411193447219/17515000000000000000000000000 : ℝ)*base66 + (1811065558917280699/437875000000000000000000000000000 : ℝ)*base67 + (3171953963627344301/437875000000000000000000000000000 : ℝ)*base70 + (141759462686655699/437875000000000000000000000000000 : ℝ)*base71 + (1958659814147/2189375000000000000000000000 : ℝ)*base73 + (4256709468591969301/437875000000000000000000000000000 : ℝ)*base76 + (400963261513719301/437875000000000000000000000000000 : ℝ)*base78 + (4504506722651594301/437875000000000000000000000000000 : ℝ)*base80 + (43086327206669/17515000000000000000000000000 : ℝ)*base82 + (1031167/500000000000000000000 : ℝ)*base89 + (1031167/500000000000000000000 : ℝ)*base91 + (1031167/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1374_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31198181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7363/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11223/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62869/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14751/25000 : ℝ) else (4007/5000 : ℝ) ≤ X j i ∧ X j i ≤ (21119/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1374_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1374_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31198181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14733/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (701/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62869/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14751/25000 : ℝ) else (4007/5000 : ℝ) ≤ X j i ∧ X j i ≤ (21119/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1374_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1374_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1374_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31198181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14733/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (701/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62869/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14751/25000 : ℝ) else (4007/5000 : ℝ) ≤ X j i ∧ X j i ≤ (21119/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1374_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
