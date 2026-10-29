-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1523_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:58:22.747074+00:00
-- url     : https://prove2.me/submissions/291df96a-9467-446d-a3e1-faeba9c11fbb

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
theorem support_rectangle_w1523_s3_0 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1851450721/10000000000 : ℝ)*x 0 + (679336549/1250000000 : ℝ)*x 1 + (1303894063/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1851450721/10000000000 : ℝ)^4543 ≤ (5666752379551/50000000000000 : ℝ)^3519 := by
    have hnat : (1851450721 : ℕ)^4543*50000000000000^3519 ≤ 5666752379551^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1851450721 10000000000 5666752379551 50000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (679336549/1250000000 : ℝ)^4543 ≤ (45510652872281/100000000000000 : ℝ)^3519 := by
    have hnat : (679336549 : ℕ)^4543*100000000000000^3519 ≤ 45510652872281^3519*1250000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679336549 1250000000 45510652872281 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303894063/2500000000 : ℝ)^4543 ≤ (8631168470617/20000000000000 : ℝ)^3519 := by
    have hnat : (1303894063 : ℕ)^4543*20000000000000^3519 ≤ 8631168470617^3519*2500000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303894063 2500000000 8631168470617 20000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1851450721/10000000000 : ℝ), (679336549/1250000000 : ℝ), (1303894063/2500000000 : ℝ)] ![(5666752379551/50000000000000 : ℝ), (45510652872281/100000000000000 : ℝ), (8631168470617/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1851450721/10000000000 : ℝ)|^4543 ≤ (5666752379551/50000000000000 : ℝ)^3519
        have hw : |(-1851450721/10000000000 : ℝ)|=(1851450721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(679336549/1250000000 : ℝ)|^4543 ≤ (45510652872281/100000000000000 : ℝ)^3519
        have hw : |(679336549/1250000000 : ℝ)|=(679336549/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1303894063/2500000000 : ℝ)|^4543 ≤ (8631168470617/20000000000000 : ℝ)^3519
        have hw : |(1303894063/2500000000 : ℝ)|=(1303894063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s3_1 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675864717/5000000000 : ℝ)*x 0 + (-122732127/625000000 : ℝ)*x 1 + (2607788287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675864717/5000000000 : ℝ)^4543 ≤ (22307874260959/50000000000000 : ℝ)^3519 := by
    have hnat : (2675864717 : ℕ)^4543*50000000000000^3519 ≤ 22307874260959^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675864717 5000000000 22307874260959 50000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (122732127/625000000 : ℝ)^4543 ≤ (3057101419371/25000000000000 : ℝ)^3519 := by
    have hnat : (122732127 : ℕ)^4543*25000000000000^3519 ≤ 3057101419371^3519*625000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122732127 625000000 3057101419371 25000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607788287/5000000000 : ℝ)^4543 ≤ (21577922896377/50000000000000 : ℝ)^3519 := by
    have hnat : (2607788287 : ℕ)^4543*50000000000000^3519 ≤ 21577922896377^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607788287 5000000000 21577922896377 50000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675864717/5000000000 : ℝ), (-122732127/625000000 : ℝ), (2607788287/5000000000 : ℝ)] ![(22307874260959/50000000000000 : ℝ), (3057101419371/25000000000000 : ℝ), (21577922896377/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675864717/5000000000 : ℝ)|^4543 ≤ (22307874260959/50000000000000 : ℝ)^3519
        have hw : |(2675864717/5000000000 : ℝ)|=(2675864717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-122732127/625000000 : ℝ)|^4543 ≤ (3057101419371/25000000000000 : ℝ)^3519
        have hw : |(-122732127/625000000 : ℝ)|=(122732127/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607788287/5000000000 : ℝ)|^4543 ≤ (21577922896377/50000000000000 : ℝ)^3519
        have hw : |(2607788287/5000000000 : ℝ)|=(2607788287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s3_2 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675864711/5000000000 : ℝ)*x 0 + (1043115299/2000000000 : ℝ)*x 1 + (-1963714151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675864711/5000000000 : ℝ)^4543 ≤ (44615748392767/100000000000000 : ℝ)^3519 := by
    have hnat : (2675864711 : ℕ)^4543*100000000000000^3519 ≤ 44615748392767^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675864711 5000000000 44615748392767 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043115299/2000000000 : ℝ)^4543 ≤ (2157792247443/5000000000000 : ℝ)^3519 := by
    have hnat : (1043115299 : ℕ)^4543*5000000000000^3519 ≤ 2157792247443^3519*2000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043115299 2000000000 2157792247443 5000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1963714151/10000000000 : ℝ)^4543 ≤ (6114203317077/50000000000000 : ℝ)^3519 := by
    have hnat : (1963714151 : ℕ)^4543*50000000000000^3519 ≤ 6114203317077^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1963714151 10000000000 6114203317077 50000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675864711/5000000000 : ℝ), (1043115299/2000000000 : ℝ), (-1963714151/10000000000 : ℝ)] ![(44615748392767/100000000000000 : ℝ), (2157792247443/5000000000000 : ℝ), (6114203317077/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675864711/5000000000 : ℝ)|^4543 ≤ (44615748392767/100000000000000 : ℝ)^3519
        have hw : |(2675864711/5000000000 : ℝ)|=(2675864711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043115299/2000000000 : ℝ)|^4543 ≤ (2157792247443/5000000000000 : ℝ)^3519
        have hw : |(1043115299/2000000000 : ℝ)|=(1043115299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1963714151/10000000000 : ℝ)|^4543 ≤ (6114203317077/50000000000000 : ℝ)^3519
        have hw : |(-1963714151/10000000000 : ℝ)|=(1963714151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s3_3 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53305039/125000000 : ℝ)*x 0 + (804045201/2000000000 : ℝ)*x 1 + (1130236109/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53305039/125000000 : ℝ)^4543 ≤ (33277451121563/100000000000000 : ℝ)^3519 := by
    have hnat : (53305039 : ℕ)^4543*100000000000000^3519 ≤ 33277451121563^3519*125000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53305039 125000000 33277451121563 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (804045201/2000000000 : ℝ)^4543 ≤ (7709578322893/25000000000000 : ℝ)^3519 := by
    have hnat : (804045201 : ℕ)^4543*25000000000000^3519 ≤ 7709578322893^3519*2000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804045201 2000000000 7709578322893 25000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1130236109/2500000000 : ℝ)^4543 ≤ (17942117783097/50000000000000 : ℝ)^3519 := by
    have hnat : (1130236109 : ℕ)^4543*50000000000000^3519 ≤ 17942117783097^3519*2500000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130236109 2500000000 17942117783097 50000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53305039/125000000 : ℝ), (804045201/2000000000 : ℝ), (1130236109/2500000000 : ℝ)] ![(33277451121563/100000000000000 : ℝ), (7709578322893/25000000000000 : ℝ), (17942117783097/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53305039/125000000 : ℝ)|^4543 ≤ (33277451121563/100000000000000 : ℝ)^3519
        have hw : |(53305039/125000000 : ℝ)|=(53305039/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(804045201/2000000000 : ℝ)|^4543 ≤ (7709578322893/25000000000000 : ℝ)^3519
        have hw : |(804045201/2000000000 : ℝ)|=(804045201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1130236109/2500000000 : ℝ)|^4543 ≤ (17942117783097/50000000000000 : ℝ)^3519
        have hw : |(1130236109/2500000000 : ℝ)|=(1130236109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s3_4 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1851481417/10000000000 : ℝ)*x 0 + (2608367747/5000000000 : ℝ)*x 1 + (5433524437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1851481417/10000000000 : ℝ)^4543 ≤ (11333747340993/100000000000000 : ℝ)^3519 := by
    have hnat : (1851481417 : ℕ)^4543*100000000000000^3519 ≤ 11333747340993^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1851481417 10000000000 11333747340993 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608367747/5000000000 : ℝ)^4543 ≤ (8633645202047/20000000000000 : ℝ)^3519 := by
    have hnat : (2608367747 : ℕ)^4543*20000000000000^3519 ≤ 8633645202047^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608367747 5000000000 8633645202047 20000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5433524437/10000000000 : ℝ)^4543 ≤ (45498026630607/100000000000000 : ℝ)^3519 := by
    have hnat : (5433524437 : ℕ)^4543*100000000000000^3519 ≤ 45498026630607^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433524437 10000000000 45498026630607 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1851481417/10000000000 : ℝ), (2608367747/5000000000 : ℝ), (5433524437/10000000000 : ℝ)] ![(11333747340993/100000000000000 : ℝ), (8633645202047/20000000000000 : ℝ), (45498026630607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1851481417/10000000000 : ℝ)|^4543 ≤ (11333747340993/100000000000000 : ℝ)^3519
        have hw : |(-1851481417/10000000000 : ℝ)|=(1851481417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608367747/5000000000 : ℝ)|^4543 ≤ (8633645202047/20000000000000 : ℝ)^3519
        have hw : |(2608367747/5000000000 : ℝ)|=(2608367747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5433524437/10000000000 : ℝ)|^4543 ≤ (45498026630607/100000000000000 : ℝ)^3519
        have hw : |(5433524437/10000000000 : ℝ)|=(5433524437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s3_5 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323528509/2500000000 : ℝ)*x 0 + (-27277593/156250000 : ℝ)*x 1 + (2716762261/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323528509/2500000000 : ℝ)^4543 ≤ (43996630381643/100000000000000 : ℝ)^3519 := by
    have hnat : (1323528509 : ℕ)^4543*100000000000000^3519 ≤ 43996630381643^3519*2500000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323528509 2500000000 43996630381643 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27277593/156250000 : ℝ)^4543 ≤ (5252671025159/50000000000000 : ℝ)^3519 := by
    have hnat : (27277593 : ℕ)^4543*50000000000000^3519 ≤ 5252671025159^3519*156250000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27277593 156250000 5252671025159 50000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716762261/5000000000 : ℝ)^4543 ≤ (1819921101979/4000000000000 : ℝ)^3519 := by
    have hnat : (2716762261 : ℕ)^4543*4000000000000^3519 ≤ 1819921101979^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716762261 5000000000 1819921101979 4000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323528509/2500000000 : ℝ), (-27277593/156250000 : ℝ), (2716762261/5000000000 : ℝ)] ![(43996630381643/100000000000000 : ℝ), (5252671025159/50000000000000 : ℝ), (1819921101979/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323528509/2500000000 : ℝ)|^4543 ≤ (43996630381643/100000000000000 : ℝ)^3519
        have hw : |(1323528509/2500000000 : ℝ)|=(1323528509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-27277593/156250000 : ℝ)|^4543 ≤ (5252671025159/50000000000000 : ℝ)^3519
        have hw : |(-27277593/156250000 : ℝ)|=(27277593/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716762261/5000000000 : ℝ)|^4543 ≤ (1819921101979/4000000000000 : ℝ)^3519
        have hw : |(2716762261/5000000000 : ℝ)|=(2716762261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s3_6 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647057007/5000000000 : ℝ)*x 0 + (2716762281/5000000000 : ℝ)*x 1 + (-1745765927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647057007/5000000000 : ℝ)^4543 ≤ (4399663014561/10000000000000 : ℝ)^3519 := by
    have hnat : (2647057007 : ℕ)^4543*10000000000000^3519 ≤ 4399663014561^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647057007 5000000000 4399663014561 10000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716762281/5000000000 : ℝ)^4543 ≤ (11374506995471/25000000000000 : ℝ)^3519 := by
    have hnat : (2716762281 : ℕ)^4543*25000000000000^3519 ≤ 11374506995471^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716762281 5000000000 11374506995471 25000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1745765927/10000000000 : ℝ)^4543 ≤ (10505341856101/100000000000000 : ℝ)^3519 := by
    have hnat : (1745765927 : ℕ)^4543*100000000000000^3519 ≤ 10505341856101^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1745765927 10000000000 10505341856101 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647057007/5000000000 : ℝ), (2716762281/5000000000 : ℝ), (-1745765927/10000000000 : ℝ)] ![(4399663014561/10000000000000 : ℝ), (11374506995471/25000000000000 : ℝ), (10505341856101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647057007/5000000000 : ℝ)|^4543 ≤ (4399663014561/10000000000000 : ℝ)^3519
        have hw : |(2647057007/5000000000 : ℝ)|=(2647057007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716762281/5000000000 : ℝ)|^4543 ≤ (11374506995471/25000000000000 : ℝ)^3519
        have hw : |(2716762281/5000000000 : ℝ)|=(2716762281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1745765927/10000000000 : ℝ)|^4543 ≤ (10505341856101/100000000000000 : ℝ)^3519
        have hw : |(-1745765927/10000000000 : ℝ)|=(1745765927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s3_7 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2132236549/5000000000 : ℝ)*x 0 + (2259147821/5000000000 : ℝ)*x 1 + (2011447579/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2132236549/5000000000 : ℝ)^4543 ≤ (2079884756453/6250000000000 : ℝ)^3519 := by
    have hnat : (2132236549 : ℕ)^4543*6250000000000^3519 ≤ 2079884756453^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132236549 5000000000 2079884756453 6250000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2259147821/5000000000 : ℝ)^4543 ≤ (35857095609189/100000000000000 : ℝ)^3519 := by
    have hnat : (2259147821 : ℕ)^4543*100000000000000^3519 ≤ 35857095609189^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259147821 5000000000 35857095609189 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2011447579/5000000000 : ℝ)^4543 ≤ (964523383571/3125000000000 : ℝ)^3519 := by
    have hnat : (2011447579 : ℕ)^4543*3125000000000^3519 ≤ 964523383571^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011447579 5000000000 964523383571 3125000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2132236549/5000000000 : ℝ), (2259147821/5000000000 : ℝ), (2011447579/5000000000 : ℝ)] ![(2079884756453/6250000000000 : ℝ), (35857095609189/100000000000000 : ℝ), (964523383571/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2132236549/5000000000 : ℝ)|^4543 ≤ (2079884756453/6250000000000 : ℝ)^3519
        have hw : |(2132236549/5000000000 : ℝ)|=(2132236549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2259147821/5000000000 : ℝ)|^4543 ≤ (35857095609189/100000000000000 : ℝ)^3519
        have hw : |(2259147821/5000000000 : ℝ)|=(2259147821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2011447579/5000000000 : ℝ)|^4543 ≤ (964523383571/3125000000000 : ℝ)^3519
        have hw : |(2011447579/5000000000 : ℝ)|=(2011447579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1523_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41064659/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3989/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10523/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5451/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15543/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3989/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10523/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3989/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10523/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3989/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10523/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3989/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10523/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3989/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10523/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3989/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10523/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10523/100000 : ℝ) ^ (4541/1024 : ℝ) ≤ (1152256529418261/25000000000000000000 : ℝ) := by
    have hpowers : (10523/100000 : ℝ)^4541 ≤ (1152256529418261/25000000000000000000 : ℝ)^1024 := by
      have hnat : (10523 : ℕ)^4541*25000000000000000000^1024 ≤ 1152256529418261^1024*100000^4541 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10523 100000 1152256529418261 25000000000000000000 4541 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10523/100000 : ℝ)) (X := (1152256529418261/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4541 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3989/25000 : ℝ) ^ (4541/1024 : ℝ) ≤ (29195139595497173/100000000000000000000 : ℝ) := by
    have hpowers : (3989/25000 : ℝ)^4541 ≤ (29195139595497173/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3989 : ℕ)^4541*100000000000000000000^1024 ≤ 29195139595497173^1024*25000^4541 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3989 25000 29195139595497173 100000000000000000000 4541 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3989/25000 : ℝ)) (X := (29195139595497173/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4541 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501152256529418261/12500000000000000000 : ℝ) ≤ (250005196514289/250000000000000 : ℝ) ^ (4541/1024 : ℝ) := by
    have hpowers : (12501152256529418261/12500000000000000000 : ℝ)^1024 ≤ (250005196514289/250000000000000 : ℝ)^4541 := by
      have hnat : (12501152256529418261 : ℕ)^1024*250000000000000^4541 ≤ 250005196514289^4541*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501152256529418261 12500000000000000000 250005196514289 250000000000000 1024 4541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250005196514289/250000000000000 : ℝ)) (X := (12501152256529418261/12500000000000000000 : ℝ)) (by norm_num) 4541 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100033804165713170217/100000000000000000000 : ℝ) ≤ (10000762187518343/10000000000000000 : ℝ) ^ (4541/1024 : ℝ) := by
    have hpowers : (100033804165713170217/100000000000000000000 : ℝ)^1024 ≤ (10000762187518343/10000000000000000 : ℝ)^4541 := by
      have hnat : (100033804165713170217 : ℕ)^1024*10000000000000000^4541 ≤ 10000762187518343^4541*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100033804165713170217 100000000000000000000 10000762187518343 10000000000000000 1024 4541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000762187518343/10000000000000000 : ℝ)) (X := (100033804165713170217/100000000000000000000 : ℝ)) (by norm_num) 4541 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029195139595497173/50000000000000000000 : ℝ) ≤ (5000658257232563/5000000000000000 : ℝ) ^ (4541/1024 : ℝ) := by
    have hpowers : (50029195139595497173/50000000000000000000 : ℝ)^1024 ≤ (5000658257232563/5000000000000000 : ℝ)^4541 := by
      have hnat : (50029195139595497173 : ℕ)^1024*5000000000000000^4541 ≤ 5000658257232563^4541*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029195139595497173 50000000000000000000 5000658257232563 5000000000000000 1024 4541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000658257232563/5000000000000000 : ℝ)) (X := (50029195139595497173/50000000000000000000 : ℝ)) (by norm_num) 4541 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1152256529418261/25000000000000000000 : ℝ) ≤ ((27159731470781645231/27165000000000000000 : ℝ)+2*(554326946783/543300000000000 : ℝ)*(10523/100000 : ℝ))^(4541/1024 : ℝ) := by
    rw [show (27159731470781645231/27165000000000000000 : ℝ)+2*(554326946783/543300000000000 : ℝ)*(10523/100000 : ℝ)=(250005196514289/250000000000000 : ℝ) by norm_num, show 1+2*(1152256529418261/25000000000000000000 : ℝ)=(12501152256529418261/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29195139595497173/100000000000000000000 : ℝ)+(1152256529418261/25000000000000000000 : ℝ) ≤ ((27159731470781645231/27165000000000000000 : ℝ)+(554326946783/543300000000000 : ℝ)*((3989/25000 : ℝ)+(10523/100000 : ℝ)))^(4541/1024 : ℝ) := by
    rw [show (27159731470781645231/27165000000000000000 : ℝ)+(554326946783/543300000000000 : ℝ)*((3989/25000 : ℝ)+(10523/100000 : ℝ))=(10000762187518343/10000000000000000 : ℝ) by norm_num, show 1+(29195139595497173/100000000000000000000 : ℝ)+(1152256529418261/25000000000000000000 : ℝ)=(100033804165713170217/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29195139595497173/100000000000000000000 : ℝ) ≤ ((27159731470781645231/27165000000000000000 : ℝ)+2*(554326946783/543300000000000 : ℝ)*(3989/25000 : ℝ))^(4541/1024 : ℝ) := by
    rw [show (27159731470781645231/27165000000000000000 : ℝ)+2*(554326946783/543300000000000 : ℝ)*(3989/25000 : ℝ)=(5000658257232563/5000000000000000 : ℝ) by norm_num, show 1+2*(29195139595497173/100000000000000000000 : ℝ)=(50029195139595497173/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27159731470781645231/27165000000000000000 : ℝ)*(X 1 0+X 2 0)+(554326946783/543300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4541/1024 : ℝ)) (lo := (10523/100000 : ℝ)) (hi := (3989/25000 : ℝ)) (c := (27159731470781645231/27165000000000000000 : ℝ)) (alpha := (554326946783/543300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27159731470781645231/27165000000000000000 : ℝ)*(X 0 1+X 2 1)+(554326946783/543300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4541/1024 : ℝ)) (lo := (10523/100000 : ℝ)) (hi := (3989/25000 : ℝ)) (c := (27159731470781645231/27165000000000000000 : ℝ)) (alpha := (554326946783/543300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27159731470781645231/27165000000000000000 : ℝ)*(X 0 2+X 1 2)+(554326946783/543300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4541/1024 : ℝ)) (lo := (10523/100000 : ℝ)) (hi := (3989/25000 : ℝ)) (c := (27159731470781645231/27165000000000000000 : ℝ)) (alpha := (554326946783/543300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1851450721/10000000000 : ℝ)*X 0 0+(679336549/1250000000 : ℝ)*X 0 1+(1303894063/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675864717/5000000000 : ℝ)*X 1 0+(-122732127/625000000 : ℝ)*X 1 1+(2607788287/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675864711/5000000000 : ℝ)*X 2 0+(1043115299/2000000000 : ℝ)*X 2 1+(-1963714151/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((53305039/125000000 : ℝ)*X 0 0+(804045201/2000000000 : ℝ)*X 0 1+(1130236109/2500000000 : ℝ)*X 0 2+(53305039/125000000 : ℝ)*X 1 0+(804045201/2000000000 : ℝ)*X 1 1+(1130236109/2500000000 : ℝ)*X 1 2+(53305039/125000000 : ℝ)*X 2 0+(804045201/2000000000 : ℝ)*X 2 1+(1130236109/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1851481417/10000000000 : ℝ)*X 0 0+(2608367747/5000000000 : ℝ)*X 0 1+(5433524437/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323528509/2500000000 : ℝ)*X 1 0+(-27277593/156250000 : ℝ)*X 1 1+(2716762261/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647057007/5000000000 : ℝ)*X 2 0+(2716762281/5000000000 : ℝ)*X 2 1+(-1745765927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2132236549/5000000000 : ℝ)*X 0 0+(2259147821/5000000000 : ℝ)*X 0 1+(2011447579/5000000000 : ℝ)*X 0 2+(2132236549/5000000000 : ℝ)*X 1 0+(2259147821/5000000000 : ℝ)*X 1 1+(2011447579/5000000000 : ℝ)*X 1 2+(2132236549/5000000000 : ℝ)*X 2 0+(2259147821/5000000000 : ℝ)*X 2 1+(2011447579/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1897248604306515773109341853/226375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1356826427/100000000000000 : ℝ)*(base19) + (1269978907/100000000000000 : ℝ)*(base23) + (41001839/100000000000000 : ℝ)*(lower2) + (62614293/20000000000000 : ℝ)*(upper3) + (4404781/3125000000000 : ℝ)*(upper5) + (1640247746283363/50000000000000 : ℝ)*(major0) + (1640247746283363/50000000000000 : ℝ)*(major1) + (1640247746283363/50000000000000 : ℝ)*(major2) + (285238501231283/6250000000000 : ℝ)*(sp0) + (91276736525537/2000000000000 : ℝ)*(sp1) + (4563836913124371/100000000000000 : ℝ)*(sp2) + (998570195208523/50000000000000 : ℝ)*(sp3) + (22163402749/100000000000000 : ℝ)*(sp4) + (12132246497/100000000000000 : ℝ)*(sp7) + (1997152522663543/100000000000000 : ℝ)*(f.failure) + (4563838183103277/100000000000000 : ℝ)*(f.sum) + (1635445116211/9055000000000000000000000000 : ℝ)*base65 + (507314291338513951/452750000000000000000000000000000 : ℝ)*base67 + (2215729152740236049/452750000000000000000000000000000 : ℝ)*base70 + (1585350918971486049/452750000000000000000000000000000 : ℝ)*base72 + (20138091282883/4527500000000000000000000000 : ℝ)*base73 + (4690802981099513951/452750000000000000000000000000000 : ℝ)*base75 + (2240996603691986049/452750000000000000000000000000000 : ℝ)*base78 + (2315040317084736049/452750000000000000000000000000000 : ℝ)*base80 + (12186273097369/9055000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (15026837/2500000000000000000000 : ℝ)*base89 + (15026837/2500000000000000000000 : ℝ)*base91 + (15026837/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24541943608362705623513/9055000000000000000000000000 : ℝ) := by norm_num
    linear_combination (360721133/100000000000000 : ℝ)*(base19) + (105238371/25000000000000 : ℝ)*(base23) + (27970213/100000000000000 : ℝ)*(upper2) + (84706187/100000000000000 : ℝ)*(upper3) + (16845747/50000000000000 : ℝ)*(upper5) + (1657837183424377/50000000000000 : ℝ)*(major0) + (1657837183424377/50000000000000 : ℝ)*(major1) + (1657837183424377/50000000000000 : ℝ)*(major2) + (1367584077/25000000000000 : ℝ)*(sp1) + (791162561/10000000000000 : ℝ)*(sp2) + (1153194840715747/25000000000000 : ℝ)*(sp4) + (4612773531805547/100000000000000 : ℝ)*(sp5) + (922554206056779/20000000000000 : ℝ)*(sp6) + (2018569280490527/100000000000000 : ℝ)*(sp7) + (2018569280490527/100000000000000 : ℝ)*(f.failure) + (1153194840715747/25000000000000 : ℝ)*(f.sum) + (38021818320283/6791250000000000000000000000 : ℝ)*base65 + (4053398643402917971/452750000000000000000000000000000 : ℝ)*base68 + (1468916881203082029/452750000000000000000000000000000 : ℝ)*base69 + (2308503730636082029/452750000000000000000000000000000 : ℝ)*base71 + (388577103527/424453125000000000000000000 : ℝ)*base74 + (3459599445364417971/452750000000000000000000000000000 : ℝ)*base76 + (3392453066824582029/452750000000000000000000000000000 : ℝ)*base77 + (5462841026139917971/452750000000000000000000000000000 : ℝ)*base80 + (105959287545367/27165000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (6014707/2500000000000000000000 : ℝ)*base90 + (6014707/2500000000000000000000 : ℝ)*base92 + (6014707/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1523_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41064659/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3989/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10523/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5451/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15543/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1523_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1523_s4_0 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1851838539/10000000000 : ℝ)*x 0 + (2716070867/5000000000 : ℝ)*x 1 + (5217870399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1851838539/10000000000 : ℝ)^4543 ≤ (11336569662153/100000000000000 : ℝ)^3519 := by
    have hnat : (1851838539 : ℕ)^4543*100000000000000^3519 ≤ 11336569662153^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1851838539 10000000000 11336569662153 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716070867/5000000000 : ℝ)^4543 ≤ (45483079864797/100000000000000 : ℝ)^3519 := by
    have hnat : (2716070867 : ℕ)^4543*100000000000000^3519 ≤ 45483079864797^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716070867 5000000000 45483079864797 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217870399/10000000000 : ℝ)^4543 ≤ (4318035046199/10000000000000 : ℝ)^3519 := by
    have hnat : (5217870399 : ℕ)^4543*10000000000000^3519 ≤ 4318035046199^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217870399 10000000000 4318035046199 10000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1851838539/10000000000 : ℝ), (2716070867/5000000000 : ℝ), (5217870399/10000000000 : ℝ)] ![(11336569662153/100000000000000 : ℝ), (45483079864797/100000000000000 : ℝ), (4318035046199/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1851838539/10000000000 : ℝ)|^4543 ≤ (11336569662153/100000000000000 : ℝ)^3519
        have hw : |(-1851838539/10000000000 : ℝ)|=(1851838539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716070867/5000000000 : ℝ)|^4543 ≤ (45483079864797/100000000000000 : ℝ)^3519
        have hw : |(2716070867/5000000000 : ℝ)|=(2716070867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217870399/10000000000 : ℝ)|^4543 ≤ (4318035046199/10000000000000 : ℝ)^3519
        have hw : |(5217870399/10000000000 : ℝ)|=(5217870399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s4_1 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070211961/2000000000 : ℝ)*x 0 + (-245195251/1250000000 : ℝ)*x 1 + (2608935201/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070211961/2000000000 : ℝ)^4543 ≤ (44608541698987/100000000000000 : ℝ)^3519 := by
    have hnat : (1070211961 : ℕ)^4543*100000000000000^3519 ≤ 44608541698987^3519*2000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070211961 2000000000 44608541698987 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (245195251/1250000000 : ℝ)^4543 ≤ (6105553898263/50000000000000 : ℝ)^3519 := by
    have hnat : (245195251 : ℕ)^4543*50000000000000^3519 ≤ 6105553898263^3519*1250000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245195251 1250000000 6105553898263 50000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608935201/5000000000 : ℝ)^4543 ≤ (43180350494041/100000000000000 : ℝ)^3519 := by
    have hnat : (2608935201 : ℕ)^4543*100000000000000^3519 ≤ 43180350494041^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608935201 5000000000 43180350494041 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070211961/2000000000 : ℝ), (-245195251/1250000000 : ℝ), (2608935201/5000000000 : ℝ)] ![(44608541698987/100000000000000 : ℝ), (6105553898263/50000000000000 : ℝ), (43180350494041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070211961/2000000000 : ℝ)|^4543 ≤ (44608541698987/100000000000000 : ℝ)^3519
        have hw : |(1070211961/2000000000 : ℝ)|=(1070211961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-245195251/1250000000 : ℝ)|^4543 ≤ (6105553898263/50000000000000 : ℝ)^3519
        have hw : |(-245195251/1250000000 : ℝ)|=(245195251/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608935201/5000000000 : ℝ)|^4543 ≤ (43180350494041/100000000000000 : ℝ)^3519
        have hw : |(2608935201/5000000000 : ℝ)|=(2608935201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s4_2 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351059741/10000000000 : ℝ)*x 0 + (5217870781/10000000000 : ℝ)*x 1 + (-196156159/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351059741/10000000000 : ℝ)^4543 ≤ (8921708202041/20000000000000 : ℝ)^3519 := by
    have hnat : (5351059741 : ℕ)^4543*20000000000000^3519 ≤ 8921708202041^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351059741 10000000000 8921708202041 20000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217870781/10000000000 : ℝ)^4543 ≤ (43180354543113/100000000000000 : ℝ)^3519 := by
    have hnat : (5217870781 : ℕ)^4543*100000000000000^3519 ≤ 43180354543113^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217870781 10000000000 43180354543113 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (196156159/1000000000 : ℝ)^4543 ≤ (2442220887439/20000000000000 : ℝ)^3519 := by
    have hnat : (196156159 : ℕ)^4543*20000000000000^3519 ≤ 2442220887439^3519*1000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196156159 1000000000 2442220887439 20000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351059741/10000000000 : ℝ), (5217870781/10000000000 : ℝ), (-196156159/1000000000 : ℝ)] ![(8921708202041/20000000000000 : ℝ), (43180354543113/100000000000000 : ℝ), (2442220887439/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351059741/10000000000 : ℝ)|^4543 ≤ (8921708202041/20000000000000 : ℝ)^3519
        have hw : |(5351059741/10000000000 : ℝ)|=(5351059741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217870781/10000000000 : ℝ)|^4543 ≤ (43180354543113/100000000000000 : ℝ)^3519
        have hw : |(5217870781/10000000000 : ℝ)|=(5217870781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-196156159/1000000000 : ℝ)|^4543 ≤ (2442220887439/20000000000000 : ℝ)^3519
        have hw : |(-196156159/1000000000 : ℝ)|=(196156159/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s4_3 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2132322521/5000000000 : ℝ)*x 0 + (4025734561/10000000000 : ℝ)*x 1 + (2257690479/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2132322521/5000000000 : ℝ)^4543 ≤ (6655977667737/20000000000000 : ℝ)^3519 := by
    have hnat : (2132322521 : ℕ)^4543*20000000000000^3519 ≤ 6655977667737^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132322521 5000000000 6655977667737 20000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4025734561/10000000000 : ℝ)^4543 ≤ (30892874996279/100000000000000 : ℝ)^3519 := by
    have hnat : (4025734561 : ℕ)^4543*100000000000000^3519 ≤ 30892874996279^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4025734561 10000000000 30892874996279 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2257690479/5000000000 : ℝ)^4543 ≤ (35827236651597/100000000000000 : ℝ)^3519 := by
    have hnat : (2257690479 : ℕ)^4543*100000000000000^3519 ≤ 35827236651597^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257690479 5000000000 35827236651597 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2132322521/5000000000 : ℝ), (4025734561/10000000000 : ℝ), (2257690479/5000000000 : ℝ)] ![(6655977667737/20000000000000 : ℝ), (30892874996279/100000000000000 : ℝ), (35827236651597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2132322521/5000000000 : ℝ)|^4543 ≤ (6655977667737/20000000000000 : ℝ)^3519
        have hw : |(2132322521/5000000000 : ℝ)|=(2132322521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4025734561/10000000000 : ℝ)|^4543 ≤ (30892874996279/100000000000000 : ℝ)^3519
        have hw : |(4025734561/10000000000 : ℝ)|=(4025734561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2257690479/5000000000 : ℝ)|^4543 ≤ (35827236651597/100000000000000 : ℝ)^3519
        have hw : |(2257690479/5000000000 : ℝ)|=(2257690479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s4_4 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1851867701/10000000000 : ℝ)*x 0 + (20386637/39062500 : ℝ)*x 1 + (5431024579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1851867701/10000000000 : ℝ)^4543 ≤ (1133680013529/10000000000000 : ℝ)^3519 := by
    have hnat : (1851867701 : ℕ)^4543*10000000000000^3519 ≤ 1133680013529^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1851867701 10000000000 1133680013529 10000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20386637/39062500 : ℝ)^4543 ≤ (21596097706121/50000000000000 : ℝ)^3519 := by
    have hnat : (20386637 : ℕ)^4543*50000000000000^3519 ≤ 21596097706121^3519*39062500^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20386637 39062500 21596097706121 50000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431024579/10000000000 : ℝ)^4543 ≤ (45471004432707/100000000000000 : ℝ)^3519 := by
    have hnat : (5431024579 : ℕ)^4543*100000000000000^3519 ≤ 45471004432707^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431024579 10000000000 45471004432707 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1851867701/10000000000 : ℝ), (20386637/39062500 : ℝ), (5431024579/10000000000 : ℝ)] ![(1133680013529/10000000000000 : ℝ), (21596097706121/50000000000000 : ℝ), (45471004432707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1851867701/10000000000 : ℝ)|^4543 ≤ (1133680013529/10000000000000 : ℝ)^3519
        have hw : |(-1851867701/10000000000 : ℝ)|=(1851867701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(20386637/39062500 : ℝ)|^4543 ≤ (21596097706121/50000000000000 : ℝ)^3519
        have hw : |(20386637/39062500 : ℝ)|=(20386637/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431024579/10000000000 : ℝ)|^4543 ≤ (45471004432707/100000000000000 : ℝ)^3519
        have hw : |(5431024579/10000000000 : ℝ)|=(5431024579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s4_5 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323679891/2500000000 : ℝ)*x 0 + (-218550939/1250000000 : ℝ)*x 1 + (5431024623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323679891/2500000000 : ℝ)^4543 ≤ (11000781763823/25000000000000 : ℝ)^3519 := by
    have hnat : (1323679891 : ℕ)^4543*25000000000000^3519 ≤ 11000781763823^3519*2500000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323679891 2500000000 11000781763823 25000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218550939/1250000000 : ℝ)^4543 ≤ (2105173604109/20000000000000 : ℝ)^3519 := by
    have hnat : (218550939 : ℕ)^4543*20000000000000^3519 ≤ 2105173604109^3519*1250000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218550939 1250000000 2105173604109 20000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431024623/10000000000 : ℝ)^4543 ≤ (45471004908293/100000000000000 : ℝ)^3519 := by
    have hnat : (5431024623 : ℕ)^4543*100000000000000^3519 ≤ 45471004908293^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431024623 10000000000 45471004908293 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323679891/2500000000 : ℝ), (-218550939/1250000000 : ℝ), (5431024623/10000000000 : ℝ)] ![(11000781763823/25000000000000 : ℝ), (2105173604109/20000000000000 : ℝ), (45471004908293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323679891/2500000000 : ℝ)|^4543 ≤ (11000781763823/25000000000000 : ℝ)^3519
        have hw : |(1323679891/2500000000 : ℝ)|=(1323679891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-218550939/1250000000 : ℝ)|^4543 ≤ (2105173604109/20000000000000 : ℝ)^3519
        have hw : |(-218550939/1250000000 : ℝ)|=(218550939/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431024623/10000000000 : ℝ)|^4543 ≤ (45471004908293/100000000000000 : ℝ)^3519
        have hw : |(5431024623/10000000000 : ℝ)|=(5431024623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s4_6 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294719553/10000000000 : ℝ)*x 0 + (5431024641/10000000000 : ℝ)*x 1 + (-874203751/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294719553/10000000000 : ℝ)^4543 ≤ (44003126937271/100000000000000 : ℝ)^3519 := by
    have hnat : (5294719553 : ℕ)^4543*100000000000000^3519 ≤ 44003126937271^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294719553 10000000000 44003126937271 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5431024641/10000000000 : ℝ)^4543 ≤ (45471005102851/100000000000000 : ℝ)^3519 := by
    have hnat : (5431024641 : ℕ)^4543*100000000000000^3519 ≤ 45471005102851^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431024641 10000000000 45471005102851 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (874203751/5000000000 : ℝ)^4543 ≤ (1315733492853/12500000000000 : ℝ)^3519 := by
    have hnat : (874203751 : ℕ)^4543*12500000000000^3519 ≤ 1315733492853^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874203751 5000000000 1315733492853 12500000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294719553/10000000000 : ℝ), (5431024641/10000000000 : ℝ), (-874203751/5000000000 : ℝ)] ![(44003126937271/100000000000000 : ℝ), (45471005102851/100000000000000 : ℝ), (1315733492853/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294719553/10000000000 : ℝ)|^4543 ≤ (44003126937271/100000000000000 : ℝ)^3519
        have hw : |(5294719553/10000000000 : ℝ)|=(5294719553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5431024641/10000000000 : ℝ)|^4543 ≤ (45471005102851/100000000000000 : ℝ)^3519
        have hw : |(5431024641/10000000000 : ℝ)|=(5431024641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-874203751/5000000000 : ℝ)|^4543 ≤ (1315733492853/12500000000000 : ℝ)^3519
        have hw : |(-874203751/5000000000 : ℝ)|=(874203751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s4_7 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1066177737/2500000000 : ℝ)*x 0 + (902569507/2000000000 : ℝ)*x 1 + (25176791/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1066177737/2500000000 : ℝ)^4543 ≤ (16640276154277/50000000000000 : ℝ)^3519 := by
    have hnat : (1066177737 : ℕ)^4543*50000000000000^3519 ≤ 16640276154277^3519*2500000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066177737 2500000000 16640276154277 50000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (902569507/2000000000 : ℝ)^4543 ≤ (3580128800953/10000000000000 : ℝ)^3519 := by
    have hnat : (902569507 : ℕ)^4543*10000000000000^3519 ≤ 3580128800953^3519*2000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902569507 2000000000 3580128800953 10000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25176791/62500000 : ℝ)^4543 ≤ (3091815966159/10000000000000 : ℝ)^3519 := by
    have hnat : (25176791 : ℕ)^4543*10000000000000^3519 ≤ 3091815966159^3519*62500000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25176791 62500000 3091815966159 10000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1066177737/2500000000 : ℝ), (902569507/2000000000 : ℝ), (25176791/62500000 : ℝ)] ![(16640276154277/50000000000000 : ℝ), (3580128800953/10000000000000 : ℝ), (3091815966159/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1066177737/2500000000 : ℝ)|^4543 ≤ (16640276154277/50000000000000 : ℝ)^3519
        have hw : |(1066177737/2500000000 : ℝ)|=(1066177737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(902569507/2000000000 : ℝ)|^4543 ≤ (3580128800953/10000000000000 : ℝ)^3519
        have hw : |(902569507/2000000000 : ℝ)|=(902569507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(25176791/62500000 : ℝ)|^4543 ≤ (3091815966159/10000000000000 : ℝ)^3519
        have hw : |(25176791/62500000 : ℝ)|=(25176791/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1523_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41064659/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15543/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5451/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10951/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15543/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5451/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15543/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5451/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15543/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5451/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15543/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5451/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15543/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5451/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15543/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5451/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5451/50000 : ℝ) ^ (4541/1024 : ℝ) ≤ (5392044523542641/100000000000000000000 : ℝ) := by
    have hpowers : (5451/50000 : ℝ)^4541 ≤ (5392044523542641/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5451 : ℕ)^4541*100000000000000000000^1024 ≤ 5392044523542641^1024*50000^4541 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5451 50000 5392044523542641 100000000000000000000 4541 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5451/50000 : ℝ)) (X := (5392044523542641/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4541 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15543/100000 : ℝ) ^ (4541/1024 : ℝ) ≤ (12994944774241299/50000000000000000000 : ℝ) := by
    have hpowers : (15543/100000 : ℝ)^4541 ≤ (12994944774241299/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15543 : ℕ)^4541*50000000000000000000^1024 ≤ 12994944774241299^1024*100000^4541 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15543 100000 12994944774241299 50000000000000000000 4541 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15543/100000 : ℝ)) (X := (12994944774241299/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4541 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005392044523542641/50000000000000000000 : ℝ) ≤ (2500060793030429/2500000000000000 : ℝ) ^ (4541/1024 : ℝ) := by
    have hpowers : (50005392044523542641/50000000000000000000 : ℝ)^1024 ≤ (2500060793030429/2500000000000000 : ℝ)^4541 := by
      have hnat : (50005392044523542641 : ℕ)^1024*2500000000000000^4541 ≤ 2500060793030429^4541*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005392044523542641 50000000000000000000 2500060793030429 2500000000000000 1024 4541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500060793030429/2500000000000000 : ℝ)) (X := (50005392044523542641/50000000000000000000 : ℝ)) (by norm_num) 4541 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100031381934072025239/100000000000000000000 : ℝ) ≤ (10000707579739087/10000000000000000 : ℝ) ^ (4541/1024 : ℝ) := by
    have hpowers : (100031381934072025239/100000000000000000000 : ℝ)^1024 ≤ (10000707579739087/10000000000000000 : ℝ)^4541 := by
      have hnat : (100031381934072025239 : ℕ)^1024*10000000000000000^4541 ≤ 10000707579739087^4541*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100031381934072025239 100000000000000000000 10000707579739087 10000000000000000 1024 4541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000707579739087/10000000000000000 : ℝ)) (X := (100031381934072025239/100000000000000000000 : ℝ)) (by norm_num) 4541 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25012994944774241299/25000000000000000000 : ℝ) ≤ (5000585993678229/5000000000000000 : ℝ) ^ (4541/1024 : ℝ) := by
    have hpowers : (25012994944774241299/25000000000000000000 : ℝ)^1024 ≤ (5000585993678229/5000000000000000 : ℝ)^4541 := by
      have hnat : (25012994944774241299 : ℕ)^1024*5000000000000000^4541 ≤ 5000585993678229^4541*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012994944774241299 25000000000000000000 5000585993678229 5000000000000000 1024 4541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000585993678229/5000000000000000 : ℝ)) (X := (25012994944774241299/25000000000000000000 : ℝ)) (by norm_num) 4541 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5392044523542641/100000000000000000000 : ℝ) ≤ ((966687554544327639/966875000000000000 : ℝ)+2*(464407617371/464100000000000 : ℝ)*(5451/50000 : ℝ))^(4541/1024 : ℝ) := by
    rw [show (966687554544327639/966875000000000000 : ℝ)+2*(464407617371/464100000000000 : ℝ)*(5451/50000 : ℝ)=(2500060793030429/2500000000000000 : ℝ) by norm_num, show 1+2*(5392044523542641/100000000000000000000 : ℝ)=(50005392044523542641/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12994944774241299/50000000000000000000 : ℝ)+(5392044523542641/100000000000000000000 : ℝ) ≤ ((966687554544327639/966875000000000000 : ℝ)+(464407617371/464100000000000 : ℝ)*((15543/100000 : ℝ)+(5451/50000 : ℝ)))^(4541/1024 : ℝ) := by
    rw [show (966687554544327639/966875000000000000 : ℝ)+(464407617371/464100000000000 : ℝ)*((15543/100000 : ℝ)+(5451/50000 : ℝ))=(10000707579739087/10000000000000000 : ℝ) by norm_num, show 1+(12994944774241299/50000000000000000000 : ℝ)+(5392044523542641/100000000000000000000 : ℝ)=(100031381934072025239/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12994944774241299/50000000000000000000 : ℝ) ≤ ((966687554544327639/966875000000000000 : ℝ)+2*(464407617371/464100000000000 : ℝ)*(15543/100000 : ℝ))^(4541/1024 : ℝ) := by
    rw [show (966687554544327639/966875000000000000 : ℝ)+2*(464407617371/464100000000000 : ℝ)*(15543/100000 : ℝ)=(5000585993678229/5000000000000000 : ℝ) by norm_num, show 1+2*(12994944774241299/50000000000000000000 : ℝ)=(25012994944774241299/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (966687554544327639/966875000000000000 : ℝ)*(X 1 0+X 2 0)+(464407617371/464100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4541/1024 : ℝ)) (lo := (5451/50000 : ℝ)) (hi := (15543/100000 : ℝ)) (c := (966687554544327639/966875000000000000 : ℝ)) (alpha := (464407617371/464100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (966687554544327639/966875000000000000 : ℝ)*(X 0 1+X 2 1)+(464407617371/464100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4541/1024 : ℝ)) (lo := (5451/50000 : ℝ)) (hi := (15543/100000 : ℝ)) (c := (966687554544327639/966875000000000000 : ℝ)) (alpha := (464407617371/464100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (966687554544327639/966875000000000000 : ℝ)*(X 0 2+X 1 2)+(464407617371/464100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4541/1024 : ℝ)) (lo := (5451/50000 : ℝ)) (hi := (15543/100000 : ℝ)) (c := (966687554544327639/966875000000000000 : ℝ)) (alpha := (464407617371/464100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1851838539/10000000000 : ℝ)*X 0 0+(2716070867/5000000000 : ℝ)*X 0 1+(5217870399/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070211961/2000000000 : ℝ)*X 1 0+(-245195251/1250000000 : ℝ)*X 1 1+(2608935201/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351059741/10000000000 : ℝ)*X 2 0+(5217870781/10000000000 : ℝ)*X 2 1+(-196156159/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2132322521/5000000000 : ℝ)*X 0 0+(4025734561/10000000000 : ℝ)*X 0 1+(2257690479/5000000000 : ℝ)*X 0 2+(2132322521/5000000000 : ℝ)*X 1 0+(4025734561/10000000000 : ℝ)*X 1 1+(2257690479/5000000000 : ℝ)*X 1 2+(2132322521/5000000000 : ℝ)*X 2 0+(4025734561/10000000000 : ℝ)*X 2 1+(2257690479/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1851867701/10000000000 : ℝ)*X 0 0+(20386637/39062500 : ℝ)*X 0 1+(5431024579/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323679891/2500000000 : ℝ)*X 1 0+(-218550939/1250000000 : ℝ)*X 1 1+(5431024623/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294719553/10000000000 : ℝ)*X 2 0+(5431024641/10000000000 : ℝ)*X 2 1+(-874203751/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1066177737/2500000000 : ℝ)*X 0 0+(902569507/2000000000 : ℝ)*X 0 1+(25176791/62500000 : ℝ)*X 0 2+(1066177737/2500000000 : ℝ)*X 1 0+(902569507/2000000000 : ℝ)*X 1 1+(25176791/62500000 : ℝ)*X 1 2+(1066177737/2500000000 : ℝ)*X 2 0+(902569507/2000000000 : ℝ)*X 2 1+(25176791/62500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (284065000399718240373881997/24171875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (154380103/12500000000000 : ℝ)*(base19) + (50234639/6250000000000 : ℝ)*(base23) + (6278597/3125000000000 : ℝ)*(lower2) + (1645197/2500000000000 : ℝ)*(upper3) + (93892943/50000000000000 : ℝ)*(upper5) + (209666513246109/6250000000000 : ℝ)*(major0) + (209666513246109/6250000000000 : ℝ)*(major1) + (209666513246109/6250000000000 : ℝ)*(major2) + (2333498601739537/50000000000000 : ℝ)*(sp0) + (4667020655017427/100000000000000 : ℝ)*(sp1) + (4667021086304027/100000000000000 : ℝ)*(sp2) + (255287276046607/12500000000000 : ℝ)*(sp3) + (24686579177/100000000000000 : ℝ)*(sp4) + (3966857503/50000000000000 : ℝ)*(sp7) + (1021153071043931/50000000000000 : ℝ)*(f.failure) + (4667021890058251/100000000000000 : ℝ)*(f.sum) + (3102673130413/7735000000000000000000000000 : ℝ)*base65 + (179390762400289823/12085937500000000000000000000000 : ℝ)*base68 + (219526698617095271/24171875000000000000000000000000 : ℝ)*base70 + (74209494320626521/24171875000000000000000000000000 : ℝ)*base72 + (26924301457671/3867500000000000000000000000 : ℝ)*base74 + (150618333908664823/12085937500000000000000000000000 : ℝ)*base76 + (78358724098501521/24171875000000000000000000000000 : ℝ)*base78 + (113699911687595271/24171875000000000000000000000000 : ℝ)*base80 + (10013806349839/3867500000000000000000000000 : ℝ)*base81 + (534529/1250000000000000000000 : ℝ)*base89 + (534529/1250000000000000000000 : ℝ)*base91 + (534529/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (126685054670172051897409453/24171875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (792128811/100000000000000 : ℝ)*(base19) + (206182703/25000000000000 : ℝ)*(base23) + (16696617/12500000000000 : ℝ)*(upper3) + (264287/2500000000000 : ℝ)*(lower4) + (65813171/100000000000000 : ℝ)*(upper5) + (847461408732461/25000000000000 : ℝ)*(major0) + (847461408732461/25000000000000 : ℝ)*(major1) + (847461408732461/25000000000000 : ℝ)*(major2) + (1168632827/10000000000000 : ℝ)*(sp1) + (1379459057/10000000000000 : ℝ)*(sp2) + (2357983321799991/50000000000000 : ℝ)*(sp4) + (4715954165142901/100000000000000 : ℝ)*(sp5) + (4715952024278599/100000000000000 : ℝ)*(sp6) + (1031862225779667/50000000000000 : ℝ)*(sp7) + (1031862225779667/50000000000000 : ℝ)*(f.failure) + (2357983321799991/50000000000000 : ℝ)*(f.sum) + (14009812258063/11602500000000000000000000000 : ℝ)*base66 + (1098587042396656237/72515625000000000000000000000000 : ℝ)*base67 + (1419795712246906237/72515625000000000000000000000000 : ℝ)*base69 + (78069376114906237/72515625000000000000000000000000 : ℝ)*base71 + (91729618273217/11602500000000000000000000000 : ℝ)*base73 + (119030874185775389/9064453125000000000000000000000 : ℝ)*base75 + (287858055994773431/36257812500000000000000000000000 : ℝ)*base77 + (389193956972503903/18128906250000000000000000000000 : ℝ)*base79 + (63431215635257/11602500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (15511447/1250000000000000000000 : ℝ)*base90 + (15511447/1250000000000000000000 : ℝ)*base92 + (15511447/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1523_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41064659/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15543/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5451/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10951/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1523_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1523_s5_0 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1851884257/10000000000 : ℝ)*x 0 + (5431840827/10000000000 : ℝ)*x 1 + (2609070513/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1851884257/10000000000 : ℝ)^4543 ≤ (226738619623/2000000000000 : ℝ)^3519 := by
    have hnat : (1851884257 : ℕ)^4543*2000000000000^3519 ≤ 226738619623^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1851884257 10000000000 226738619623 2000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5431840827/10000000000 : ℝ)^4543 ≤ (11369956815497/25000000000000 : ℝ)^3519 := by
    have hnat : (5431840827 : ℕ)^4543*25000000000000^3519 ≤ 11369956815497^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431840827 10000000000 11369956815497 25000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609070513/5000000000 : ℝ)^4543 ≤ (2159162087297/5000000000000 : ℝ)^3519 := by
    have hnat : (2609070513 : ℕ)^4543*5000000000000^3519 ≤ 2159162087297^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609070513 5000000000 2159162087297 5000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1851884257/10000000000 : ℝ), (5431840827/10000000000 : ℝ), (2609070513/5000000000 : ℝ)] ![(226738619623/2000000000000 : ℝ), (11369956815497/25000000000000 : ℝ), (2159162087297/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1851884257/10000000000 : ℝ)|^4543 ≤ (226738619623/2000000000000 : ℝ)^3519
        have hw : |(-1851884257/10000000000 : ℝ)|=(1851884257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5431840827/10000000000 : ℝ)|^4543 ≤ (11369956815497/25000000000000 : ℝ)^3519
        have hw : |(5431840827/10000000000 : ℝ)|=(5431840827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609070513/5000000000 : ℝ)|^4543 ≤ (2159162087297/5000000000000 : ℝ)^3519
        have hw : |(2609070513/5000000000 : ℝ)|=(2609070513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s5_1 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070196177/2000000000 : ℝ)*x 0 + (-1961306827/10000000000 : ℝ)*x 1 + (163066933/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070196177/2000000000 : ℝ)^4543 ≤ (11151923086687/25000000000000 : ℝ)^3519 := by
    have hnat : (1070196177 : ℕ)^4543*25000000000000^3519 ≤ 11151923086687^3519*2000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070196177 2000000000 11151923086687 25000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1961306827/10000000000 : ℝ)^4543 ≤ (12209057028167/100000000000000 : ℝ)^3519 := by
    have hnat : (1961306827 : ℕ)^4543*100000000000000^3519 ≤ 12209057028167^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1961306827 10000000000 12209057028167 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163066933/312500000 : ℝ)^4543 ≤ (10795812653359/25000000000000 : ℝ)^3519 := by
    have hnat : (163066933 : ℕ)^4543*25000000000000^3519 ≤ 10795812653359^3519*312500000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163066933 312500000 10795812653359 25000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070196177/2000000000 : ℝ), (-1961306827/10000000000 : ℝ), (163066933/312500000 : ℝ)] ![(11151923086687/25000000000000 : ℝ), (12209057028167/100000000000000 : ℝ), (10795812653359/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070196177/2000000000 : ℝ)|^4543 ≤ (11151923086687/25000000000000 : ℝ)^3519
        have hw : |(1070196177/2000000000 : ℝ)|=(1070196177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1961306827/10000000000 : ℝ)|^4543 ≤ (12209057028167/100000000000000 : ℝ)^3519
        have hw : |(-1961306827/10000000000 : ℝ)|=(1961306827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163066933/312500000 : ℝ)|^4543 ≤ (10795812653359/25000000000000 : ℝ)^3519
        have hw : |(163066933/312500000 : ℝ)|=(163066933/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s5_2 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350981323/10000000000 : ℝ)*x 0 + (5218141309/10000000000 : ℝ)*x 1 + (-1961306969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350981323/10000000000 : ℝ)^4543 ≤ (44607697060579/100000000000000 : ℝ)^3519 := by
    have hnat : (5350981323 : ℕ)^4543*100000000000000^3519 ≤ 44607697060579^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350981323 10000000000 44607697060579 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218141309/10000000000 : ℝ)^4543 ≤ (10795811192359/25000000000000 : ℝ)^3519 := by
    have hnat : (5218141309 : ℕ)^4543*25000000000000^3519 ≤ 10795811192359^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218141309 10000000000 10795811192359 25000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1961306969/10000000000 : ℝ)^4543 ≤ (3052264542333/25000000000000 : ℝ)^3519 := by
    have hnat : (1961306969 : ℕ)^4543*25000000000000^3519 ≤ 3052264542333^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1961306969 10000000000 3052264542333 25000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350981323/10000000000 : ℝ), (5218141309/10000000000 : ℝ), (-1961306969/10000000000 : ℝ)] ![(44607697060579/100000000000000 : ℝ), (10795811192359/25000000000000 : ℝ), (3052264542333/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350981323/10000000000 : ℝ)|^4543 ≤ (44607697060579/100000000000000 : ℝ)^3519
        have hw : |(5350981323/10000000000 : ℝ)|=(5350981323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218141309/10000000000 : ℝ)|^4543 ≤ (10795811192359/25000000000000 : ℝ)^3519
        have hw : |(5218141309/10000000000 : ℝ)|=(5218141309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1961306969/10000000000 : ℝ)|^4543 ≤ (3052264542333/25000000000000 : ℝ)^3519
        have hw : |(-1961306969/10000000000 : ℝ)|=(1961306969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s5_3 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4264673301/10000000000 : ℝ)*x 0 + (4026385363/10000000000 : ℝ)*x 1 + (4514723713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4264673301/10000000000 : ℝ)^4543 ≤ (832004325839/2500000000000 : ℝ)^3519 := by
    have hnat : (4264673301 : ℕ)^4543*2500000000000^3519 ≤ 832004325839^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4264673301 10000000000 832004325839 2500000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4026385363/10000000000 : ℝ)^4543 ≤ (6179864512331/20000000000000 : ℝ)^3519 := by
    have hnat : (4026385363 : ℕ)^4543*20000000000000^3519 ≤ 6179864512331^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4026385363 10000000000 6179864512331 20000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4514723713/10000000000 : ℝ)^4543 ≤ (17910252198913/50000000000000 : ℝ)^3519 := by
    have hnat : (4514723713 : ℕ)^4543*50000000000000^3519 ≤ 17910252198913^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4514723713 10000000000 17910252198913 50000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4264673301/10000000000 : ℝ), (4026385363/10000000000 : ℝ), (4514723713/10000000000 : ℝ)] ![(832004325839/2500000000000 : ℝ), (6179864512331/20000000000000 : ℝ), (17910252198913/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4264673301/10000000000 : ℝ)|^4543 ≤ (832004325839/2500000000000 : ℝ)^3519
        have hw : |(4264673301/10000000000 : ℝ)|=(4264673301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4026385363/10000000000 : ℝ)|^4543 ≤ (6179864512331/20000000000000 : ℝ)^3519
        have hw : |(4026385363/10000000000 : ℝ)|=(4026385363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4514723713/10000000000 : ℝ)|^4543 ≤ (17910252198913/50000000000000 : ℝ)^3519
        have hw : |(4514723713/10000000000 : ℝ)|=(4514723713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s5_4 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-185191291/1000000000 : ℝ)*x 0 + (2609622149/5000000000 : ℝ)*x 1 + (5430729349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (185191291/1000000000 : ℝ)^4543 ≤ (1417144679147/12500000000000 : ℝ)^3519 := by
    have hnat : (185191291 : ℕ)^4543*12500000000000^3519 ≤ 1417144679147^3519*1000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      185191291 1000000000 1417144679147 12500000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609622149/5000000000 : ℝ)^4543 ≤ (8639005833711/20000000000000 : ℝ)^3519 := by
    have hnat : (2609622149 : ℕ)^4543*20000000000000^3519 ≤ 8639005833711^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609622149 5000000000 8639005833711 20000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5430729349/10000000000 : ℝ)^4543 ≤ (45467813384971/100000000000000 : ℝ)^3519 := by
    have hnat : (5430729349 : ℕ)^4543*100000000000000^3519 ≤ 45467813384971^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430729349 10000000000 45467813384971 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-185191291/1000000000 : ℝ), (2609622149/5000000000 : ℝ), (5430729349/10000000000 : ℝ)] ![(1417144679147/12500000000000 : ℝ), (8639005833711/20000000000000 : ℝ), (45467813384971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-185191291/1000000000 : ℝ)|^4543 ≤ (1417144679147/12500000000000 : ℝ)^3519
        have hw : |(-185191291/1000000000 : ℝ)|=(185191291/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609622149/5000000000 : ℝ)|^4543 ≤ (8639005833711/20000000000000 : ℝ)^3519
        have hw : |(2609622149/5000000000 : ℝ)|=(2609622149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5430729349/10000000000 : ℝ)|^4543 ≤ (45467813384971/100000000000000 : ℝ)^3519
        have hw : |(5430729349/10000000000 : ℝ)|=(5430729349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s5_5 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058958221/2000000000 : ℝ)*x 0 + (-1748719381/10000000000 : ℝ)*x 1 + (108614587/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058958221/2000000000 : ℝ)^4543 ≤ (22001947314339/50000000000000 : ℝ)^3519 := by
    have hnat : (1058958221 : ℕ)^4543*50000000000000^3519 ≤ 22001947314339^3519*2000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058958221 2000000000 22001947314339 50000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1748719381/10000000000 : ℝ)^4543 ≤ (5264145981219/50000000000000 : ℝ)^3519 := by
    have hnat : (1748719381 : ℕ)^4543*50000000000000^3519 ≤ 5264145981219^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1748719381 10000000000 5264145981219 50000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108614587/200000000 : ℝ)^4543 ≤ (2273390669789/5000000000000 : ℝ)^3519 := by
    have hnat : (108614587 : ℕ)^4543*5000000000000^3519 ≤ 2273390669789^3519*200000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108614587 200000000 2273390669789 5000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058958221/2000000000 : ℝ), (-1748719381/10000000000 : ℝ), (108614587/200000000 : ℝ)] ![(22001947314339/50000000000000 : ℝ), (5264145981219/50000000000000 : ℝ), (2273390669789/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058958221/2000000000 : ℝ)|^4543 ≤ (22001947314339/50000000000000 : ℝ)^3519
        have hw : |(1058958221/2000000000 : ℝ)|=(1058958221/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1748719381/10000000000 : ℝ)|^4543 ≤ (5264145981219/50000000000000 : ℝ)^3519
        have hw : |(-1748719381/10000000000 : ℝ)|=(1748719381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(108614587/200000000 : ℝ)|^4543 ≤ (2273390669789/5000000000000 : ℝ)^3519
        have hw : |(108614587/200000000 : ℝ)|=(108614587/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s5_6 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647395553/5000000000 : ℝ)*x 0 + (5430729349/10000000000 : ℝ)*x 1 + (-1748719381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647395553/5000000000 : ℝ)^4543 ≤ (44003894639407/100000000000000 : ℝ)^3519 := by
    have hnat : (2647395553 : ℕ)^4543*100000000000000^3519 ≤ 44003894639407^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647395553 5000000000 44003894639407 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5430729349/10000000000 : ℝ)^4543 ≤ (45467813384971/100000000000000 : ℝ)^3519 := by
    have hnat : (5430729349 : ℕ)^4543*100000000000000^3519 ≤ 45467813384971^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430729349 10000000000 45467813384971 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1748719381/10000000000 : ℝ)^4543 ≤ (5264145981219/50000000000000 : ℝ)^3519 := by
    have hnat : (1748719381 : ℕ)^4543*50000000000000^3519 ≤ 5264145981219^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1748719381 10000000000 5264145981219 50000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647395553/5000000000 : ℝ), (5430729349/10000000000 : ℝ), (-1748719381/10000000000 : ℝ)] ![(44003894639407/100000000000000 : ℝ), (45467813384971/100000000000000 : ℝ), (5264145981219/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647395553/5000000000 : ℝ)|^4543 ≤ (44003894639407/100000000000000 : ℝ)^3519
        have hw : |(2647395553/5000000000 : ℝ)|=(2647395553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5430729349/10000000000 : ℝ)|^4543 ≤ (45467813384971/100000000000000 : ℝ)^3519
        have hw : |(5430729349/10000000000 : ℝ)|=(5430729349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1748719381/10000000000 : ℝ)|^4543 ≤ (5264145981219/50000000000000 : ℝ)^3519
        have hw : |(-1748719381/10000000000 : ℝ)|=(1748719381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s5_7 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2132369399/5000000000 : ℝ)*x 0 + (4512203629/10000000000 : ℝ)*x 1 + (4028923761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2132369399/5000000000 : ℝ)^4543 ≤ (33280832884223/100000000000000 : ℝ)^3519 := by
    have hnat : (2132369399 : ℕ)^4543*100000000000000^3519 ≤ 33280832884223^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132369399 5000000000 33280832884223 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4512203629/10000000000 : ℝ)^4543 ≤ (35794693463321/100000000000000 : ℝ)^3519 := by
    have hnat : (4512203629 : ℕ)^4543*100000000000000^3519 ≤ 35794693463321^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4512203629 10000000000 35794693463321 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4028923761/10000000000 : ℝ)^4543 ≤ (30924473641439/100000000000000 : ℝ)^3519 := by
    have hnat : (4028923761 : ℕ)^4543*100000000000000^3519 ≤ 30924473641439^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4028923761 10000000000 30924473641439 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2132369399/5000000000 : ℝ), (4512203629/10000000000 : ℝ), (4028923761/10000000000 : ℝ)] ![(33280832884223/100000000000000 : ℝ), (35794693463321/100000000000000 : ℝ), (30924473641439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2132369399/5000000000 : ℝ)|^4543 ≤ (33280832884223/100000000000000 : ℝ)^3519
        have hw : |(2132369399/5000000000 : ℝ)|=(2132369399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4512203629/10000000000 : ℝ)|^4543 ≤ (35794693463321/100000000000000 : ℝ)^3519
        have hw : |(4512203629/10000000000 : ℝ)|=(4512203629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4028923761/10000000000 : ℝ)|^4543 ≤ (30924473641439/100000000000000 : ℝ)^3519
        have hw : |(4028923761/10000000000 : ℝ)|=(4028923761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1523_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41064659/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10951/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10957/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3871/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10951/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10951/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10951/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10951/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10951/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10951/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10951/100000 : ℝ) ^ (4541/1024 : ℝ) ≤ (687543621549999/12500000000000000000 : ℝ) := by
    have hpowers : (10951/100000 : ℝ)^4541 ≤ (687543621549999/12500000000000000000 : ℝ)^1024 := by
      have hnat : (10951 : ℕ)^4541*12500000000000000000^1024 ≤ 687543621549999^1024*100000^4541 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10951 100000 687543621549999 12500000000000000000 4541 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10951/100000 : ℝ)) (X := (687543621549999/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4541 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4541/1024 : ℝ) ≤ (6399795124513657/25000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4541 ≤ (6399795124513657/25000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4541*25000000000000000000^1024 ≤ 6399795124513657^1024*10000^4541 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 6399795124513657 25000000000000000000 4541 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (6399795124513657/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4541 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250687543621549999/6250000000000000000 : ℝ) ≤ (10000248056261797/10000000000000000 : ℝ) ^ (4541/1024 : ℝ) := by
    have hpowers : (6250687543621549999/6250000000000000000 : ℝ)^1024 ≤ (10000248056261797/10000000000000000 : ℝ)^4541 := by
      have hnat : (6250687543621549999 : ℕ)^1024*10000000000000000^4541 ≤ 10000248056261797^4541*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250687543621549999 6250000000000000000 10000248056261797 10000000000000000 1024 4541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000248056261797/10000000000000000 : ℝ)) (X := (6250687543621549999/6250000000000000000 : ℝ)) (by norm_num) 4541 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5001554976473522731/5000000000000000000 : ℝ) ≤ (5000350606513883/5000000000000000 : ℝ) ^ (4541/1024 : ℝ) := by
    have hpowers : (5001554976473522731/5000000000000000000 : ℝ)^1024 ≤ (5000350606513883/5000000000000000 : ℝ)^4541 := by
      have hnat : (5001554976473522731 : ℕ)^1024*5000000000000000^4541 ≤ 5000350606513883^4541*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001554976473522731 5000000000000000000 5000350606513883 5000000000000000 1024 4541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000350606513883/5000000000000000 : ℝ)) (X := (5001554976473522731/5000000000000000000 : ℝ)) (by norm_num) 4541 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506399795124513657/12500000000000000000 : ℝ) ≤ (2000230873958747/2000000000000000 : ℝ) ^ (4541/1024 : ℝ) := by
    have hpowers : (12506399795124513657/12500000000000000000 : ℝ)^1024 ≤ (2000230873958747/2000000000000000 : ℝ)^4541 := by
      have hnat : (12506399795124513657 : ℕ)^1024*2000000000000000^4541 ≤ 2000230873958747^4541*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506399795124513657 12500000000000000000 2000230873958747 2000000000000000 1024 4541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000230873958747/2000000000000000 : ℝ)) (X := (12506399795124513657/12500000000000000000 : ℝ)) (by norm_num) 4541 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(687543621549999/12500000000000000000 : ℝ) ≤ ((3025413392525602903/3026000000000000000 : ℝ)+2*(151052255323/151300000000000 : ℝ)*(10951/100000 : ℝ))^(4541/1024 : ℝ) := by
    rw [show (3025413392525602903/3026000000000000000 : ℝ)+2*(151052255323/151300000000000 : ℝ)*(10951/100000 : ℝ)=(10000248056261797/10000000000000000 : ℝ) by norm_num, show 1+2*(687543621549999/12500000000000000000 : ℝ)=(6250687543621549999/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6399795124513657/25000000000000000000 : ℝ)+(687543621549999/12500000000000000000 : ℝ) ≤ ((3025413392525602903/3026000000000000000 : ℝ)+(151052255323/151300000000000 : ℝ)*((1549/10000 : ℝ)+(10951/100000 : ℝ)))^(4541/1024 : ℝ) := by
    rw [show (3025413392525602903/3026000000000000000 : ℝ)+(151052255323/151300000000000 : ℝ)*((1549/10000 : ℝ)+(10951/100000 : ℝ))=(5000350606513883/5000000000000000 : ℝ) by norm_num, show 1+(6399795124513657/25000000000000000000 : ℝ)+(687543621549999/12500000000000000000 : ℝ)=(5001554976473522731/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6399795124513657/25000000000000000000 : ℝ) ≤ ((3025413392525602903/3026000000000000000 : ℝ)+2*(151052255323/151300000000000 : ℝ)*(1549/10000 : ℝ))^(4541/1024 : ℝ) := by
    rw [show (3025413392525602903/3026000000000000000 : ℝ)+2*(151052255323/151300000000000 : ℝ)*(1549/10000 : ℝ)=(2000230873958747/2000000000000000 : ℝ) by norm_num, show 1+2*(6399795124513657/25000000000000000000 : ℝ)=(12506399795124513657/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3025413392525602903/3026000000000000000 : ℝ)*(X 1 0+X 2 0)+(151052255323/151300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4541/1024 : ℝ)) (lo := (10951/100000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (3025413392525602903/3026000000000000000 : ℝ)) (alpha := (151052255323/151300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3025413392525602903/3026000000000000000 : ℝ)*(X 0 1+X 2 1)+(151052255323/151300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4541/1024 : ℝ)) (lo := (10951/100000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (3025413392525602903/3026000000000000000 : ℝ)) (alpha := (151052255323/151300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3025413392525602903/3026000000000000000 : ℝ)*(X 0 2+X 1 2)+(151052255323/151300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4541/1024 : ℝ)) (lo := (10951/100000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (3025413392525602903/3026000000000000000 : ℝ)) (alpha := (151052255323/151300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1851884257/10000000000 : ℝ)*X 0 0+(5431840827/10000000000 : ℝ)*X 0 1+(2609070513/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070196177/2000000000 : ℝ)*X 1 0+(-1961306827/10000000000 : ℝ)*X 1 1+(163066933/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350981323/10000000000 : ℝ)*X 2 0+(5218141309/10000000000 : ℝ)*X 2 1+(-1961306969/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4264673301/10000000000 : ℝ)*X 0 0+(4026385363/10000000000 : ℝ)*X 0 1+(4514723713/10000000000 : ℝ)*X 0 2+(4264673301/10000000000 : ℝ)*X 1 0+(4026385363/10000000000 : ℝ)*X 1 1+(4514723713/10000000000 : ℝ)*X 1 2+(4264673301/10000000000 : ℝ)*X 2 0+(4026385363/10000000000 : ℝ)*X 2 1+(4514723713/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-185191291/1000000000 : ℝ)*X 0 0+(2609622149/5000000000 : ℝ)*X 0 1+(5430729349/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1058958221/2000000000 : ℝ)*X 1 0+(-1748719381/10000000000 : ℝ)*X 1 1+(108614587/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647395553/5000000000 : ℝ)*X 2 0+(5430729349/10000000000 : ℝ)*X 2 1+(-1748719381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2132369399/5000000000 : ℝ)*X 0 0+(4512203629/10000000000 : ℝ)*X 0 1+(4028923761/10000000000 : ℝ)*X 0 2+(2132369399/5000000000 : ℝ)*X 1 0+(4512203629/10000000000 : ℝ)*X 1 1+(4028923761/10000000000 : ℝ)*X 1 2+(2132369399/5000000000 : ℝ)*X 2 0+(4512203629/10000000000 : ℝ)*X 2 1+(4028923761/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16002253927192366693595253/2225000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1255686453/100000000000000 : ℝ)*(base19) + (1562756069/100000000000000 : ℝ)*(base23) + (40651421/100000000000000 : ℝ)*(lower2) + (8058341/5000000000000 : ℝ)*(upper3) + (14966113/50000000000000 : ℝ)*(upper5) + (840915542752963/25000000000000 : ℝ)*(major0) + (840915542752963/25000000000000 : ℝ)*(major1) + (840915542752963/25000000000000 : ℝ)*(major2) + (4679501104971689/100000000000000 : ℝ)*(sp0) + (116988469576339/2500000000000 : ℝ)*(sp1) + (4679538475983943/100000000000000 : ℝ)*(sp2) + (2047770950519079/100000000000000 : ℝ)*(sp3) + (38933768323/100000000000000 : ℝ)*(sp4) + (204891101/1562500000000 : ℝ)*(sp7) + (2047784063549543/100000000000000 : ℝ)*(f.failure) + (1169885009685003/25000000000000 : ℝ)*(f.sum) + (227337226543/111250000000000000000000000 : ℝ)*base66 + (44483596981051083/4450000000000000000000000000000 : ℝ)*base68 + (5729821825951083/4450000000000000000000000000000 : ℝ)*base70 + (70146475802501083/4450000000000000000000000000000 : ℝ)*base72 + (1415803521403/445000000000000000000000000 : ℝ)*base73 + (64041654925501083/4450000000000000000000000000000 : ℝ)*base76 + (32542622953551083/4450000000000000000000000000000 : ℝ)*base78 + (21917123349551083/4450000000000000000000000000000 : ℝ)*base80 + (403219472427/111250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (12900837/2500000000000000000000 : ℝ)*base89 + (12900837/2500000000000000000000 : ℝ)*base91 + (12900837/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7674057309361364176653/945625000000000000000000000 : ℝ) := by norm_num
    linear_combination (654409357/50000000000000 : ℝ)*(base19) + (710622199/50000000000000 : ℝ)*(base23) + (431148471/100000000000000 : ℝ)*(lower1) + (167359077/100000000000000 : ℝ)*(upper3) + (50465719/100000000000000 : ℝ)*(lower4) + (33482333/20000000000000 : ℝ)*(upper5) + (3398815417558481/100000000000000 : ℝ)*(major0) + (3398815417558481/100000000000000 : ℝ)*(major1) + (3398815417558481/100000000000000 : ℝ)*(major2) + (6113863/400000000000 : ℝ)*(sp2) + (4728445345292183/100000000000000 : ℝ)*(sp4) + (4728444036473469/100000000000000 : ℝ)*(sp5) + (945688479116407/20000000000000 : ℝ)*(sp6) + (413837043862763/20000000000000 : ℝ)*(sp7) + (413837043862763/20000000000000 : ℝ)*(f.failure) + (4728445345292183/100000000000000 : ℝ)*(f.sum) + (17585829974763/7565000000000000000000000000 : ℝ)*base65 + (576634284215662921/17800000000000000000000000000000 : ℝ)*base68 + (14737766667062921/17800000000000000000000000000000 : ℝ)*base70 + (962238006154462921/17800000000000000000000000000000 : ℝ)*base72 + (31224458627127/7565000000000000000000000000 : ℝ)*base74 + (1740409227495537079/17800000000000000000000000000000 : ℝ)*base75 + (26073623918537079/17800000000000000000000000000000 : ℝ)*base77 + (177879423912537079/17800000000000000000000000000000 : ℝ)*base79 + (60244511129087/7565000000000000000000000000 : ℝ)*base82 + (392817/500000000000000000000 : ℝ)*base89 + (392817/500000000000000000000 : ℝ)*base91 + (392817/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1523_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41064659/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10951/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10957/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1523_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1523_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41064659/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3989/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10523/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10957/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1523_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1523_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1523_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41064659/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3989/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10523/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10957/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1523_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
