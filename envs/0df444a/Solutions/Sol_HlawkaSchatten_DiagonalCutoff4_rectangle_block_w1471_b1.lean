-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1471_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:10:18.933416+00:00
-- url     : https://prove2.me/submissions/d39dd9c2-8ffc-4ae8-8b7a-7e8ed294982a

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
theorem support_rectangle_w1471_s3_0 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-6029759/31250000 : ℝ)*x 0 + (5443832749/10000000000 : ℝ)*x 1 + (5210602091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6029759/31250000 : ℝ)^4439 ≤ (11781200086099/100000000000000 : ℝ)^3415 := by
    have hnat : (6029759 : ℕ)^4439*100000000000000^3415 ≤ 11781200086099^3415*31250000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6029759 31250000 11781200086099 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5443832749/10000000000 : ℝ)^4439 ≤ (177204565841/390625000000 : ℝ)^3415 := by
    have hnat : (5443832749 : ℕ)^4439*390625000000^3415 ≤ 177204565841^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443832749 10000000000 177204565841 390625000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5210602091/10000000000 : ℝ)^4439 ≤ (10713607759271/25000000000000 : ℝ)^3415 := by
    have hnat : (5210602091 : ℕ)^4439*25000000000000^3415 ≤ 10713607759271^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5210602091 10000000000 10713607759271 25000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-6029759/31250000 : ℝ), (5443832749/10000000000 : ℝ), (5210602091/10000000000 : ℝ)] ![(11781200086099/100000000000000 : ℝ), (177204565841/390625000000 : ℝ), (10713607759271/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-6029759/31250000 : ℝ)|^4439 ≤ (11781200086099/100000000000000 : ℝ)^3415
        have hw : |(-6029759/31250000 : ℝ)|=(6029759/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5443832749/10000000000 : ℝ)|^4439 ≤ (177204565841/390625000000 : ℝ)^3415
        have hw : |(5443832749/10000000000 : ℝ)|=(5443832749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5210602091/10000000000 : ℝ)|^4439 ≤ (10713607759271/25000000000000 : ℝ)^3415
        have hw : |(5210602091/10000000000 : ℝ)|=(5210602091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_s3_1 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267755939/500000000 : ℝ)*x 0 + (-1024603077/5000000000 : ℝ)*x 1 + (1302650469/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267755939/500000000 : ℝ)^4439 ≤ (1110144626271/2500000000000 : ℝ)^3415 := by
    have hnat : (267755939 : ℕ)^4439*2500000000000^3415 ≤ 1110144626271^3415*500000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267755939 500000000 1110144626271 2500000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1024603077/5000000000 : ℝ)^4439 ≤ (12739786197233/100000000000000 : ℝ)^3415 := by
    have hnat : (1024603077 : ℕ)^4439*100000000000000^3415 ≤ 12739786197233^3415*5000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024603077 5000000000 12739786197233 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1302650469/2500000000 : ℝ)^4439 ≤ (10713607184651/25000000000000 : ℝ)^3415 := by
    have hnat : (1302650469 : ℕ)^4439*25000000000000^3415 ≤ 10713607184651^3415*2500000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1302650469 2500000000 10713607184651 25000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267755939/500000000 : ℝ), (-1024603077/5000000000 : ℝ), (1302650469/2500000000 : ℝ)] ![(1110144626271/2500000000000 : ℝ), (12739786197233/100000000000000 : ℝ), (10713607184651/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267755939/500000000 : ℝ)|^4439 ≤ (1110144626271/2500000000000 : ℝ)^3415
        have hw : |(267755939/500000000 : ℝ)|=(267755939/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1024603077/5000000000 : ℝ)|^4439 ≤ (12739786197233/100000000000000 : ℝ)^3415
        have hw : |(-1024603077/5000000000 : ℝ)|=(1024603077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1302650469/2500000000 : ℝ)|^4439 ≤ (10713607184651/25000000000000 : ℝ)^3415
        have hw : |(1302650469/2500000000 : ℝ)|=(1302650469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_s3_2 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071023791/2000000000 : ℝ)*x 0 + (2605300889/5000000000 : ℝ)*x 1 + (-40984121/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071023791/2000000000 : ℝ)^4439 ≤ (22202893468553/50000000000000 : ℝ)^3415 := by
    have hnat : (1071023791 : ℕ)^4439*50000000000000^3415 ≤ 22202893468553^3415*2000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071023791 2000000000 22202893468553 50000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2605300889/5000000000 : ℝ)^4439 ≤ (1714177107637/4000000000000 : ℝ)^3415 := by
    have hnat : (2605300889 : ℕ)^4439*4000000000000^3415 ≤ 1714177107637^3415*5000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2605300889 5000000000 1714177107637 4000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40984121/200000000 : ℝ)^4439 ≤ (6369892678399/50000000000000 : ℝ)^3415 := by
    have hnat : (40984121 : ℕ)^4439*50000000000000^3415 ≤ 6369892678399^3415*200000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40984121 200000000 6369892678399 50000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071023791/2000000000 : ℝ), (2605300889/5000000000 : ℝ), (-40984121/200000000 : ℝ)] ![(22202893468553/50000000000000 : ℝ), (1714177107637/4000000000000 : ℝ), (6369892678399/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071023791/2000000000 : ℝ)|^4439 ≤ (22202893468553/50000000000000 : ℝ)^3415
        have hw : |(1071023791/2000000000 : ℝ)|=(1071023791/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2605300889/5000000000 : ℝ)|^4439 ≤ (1714177107637/4000000000000 : ℝ)^3415
        have hw : |(2605300889/5000000000 : ℝ)|=(2605300889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-40984121/200000000 : ℝ)|^4439 ≤ (6369892678399/50000000000000 : ℝ)^3415
        have hw : |(-40984121/200000000 : ℝ)|=(40984121/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_s3_3 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4288754017/10000000000 : ℝ)*x 0 + (1009674099/2500000000 : ℝ)*x 1 + (910464729/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4288754017/10000000000 : ℝ)^4439 ≤ (266179311661/800000000000 : ℝ)^3415 := by
    have hnat : (4288754017 : ℕ)^4439*800000000000^3415 ≤ 266179311661^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4288754017 10000000000 266179311661 800000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1009674099/2500000000 : ℝ)^4439 ≤ (3846637253267/12500000000000 : ℝ)^3415 := by
    have hnat : (1009674099 : ℕ)^4439*12500000000000^3415 ≤ 3846637253267^3415*2500000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009674099 2500000000 3846637253267 12500000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (910464729/2000000000 : ℝ)^4439 ≤ (35954487994469/100000000000000 : ℝ)^3415 := by
    have hnat : (910464729 : ℕ)^4439*100000000000000^3415 ≤ 35954487994469^3415*2000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      910464729 2000000000 35954487994469 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4288754017/10000000000 : ℝ), (1009674099/2500000000 : ℝ), (910464729/2000000000 : ℝ)] ![(266179311661/800000000000 : ℝ), (3846637253267/12500000000000 : ℝ), (35954487994469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4288754017/10000000000 : ℝ)|^4439 ≤ (266179311661/800000000000 : ℝ)^3415
        have hw : |(4288754017/10000000000 : ℝ)|=(4288754017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1009674099/2500000000 : ℝ)|^4439 ≤ (3846637253267/12500000000000 : ℝ)^3415
        have hw : |(1009674099/2500000000 : ℝ)|=(1009674099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(910464729/2000000000 : ℝ)|^4439 ≤ (35954487994469/100000000000000 : ℝ)^3415
        have hw : |(910464729/2000000000 : ℝ)|=(910464729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_s3_4 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1929557899/10000000000 : ℝ)*x 0 + (1302961403/2500000000 : ℝ)*x 1 + (5442579703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1929557899/10000000000 : ℝ)^4439 ≤ (5890739009179/50000000000000 : ℝ)^3415 := by
    have hnat : (1929557899 : ℕ)^4439*50000000000000^3415 ≤ 5890739009179^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1929557899 10000000000 5890739009179 50000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1302961403/2500000000 : ℝ)^4439 ≤ (42867725503859/100000000000000 : ℝ)^3415 := by
    have hnat : (1302961403 : ℕ)^4439*100000000000000^3415 ≤ 42867725503859^3415*2500000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1302961403 2500000000 42867725503859 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5442579703/10000000000 : ℝ)^4439 ≤ (22675398229029/50000000000000 : ℝ)^3415 := by
    have hnat : (5442579703 : ℕ)^4439*50000000000000^3415 ≤ 22675398229029^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442579703 10000000000 22675398229029 50000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1929557899/10000000000 : ℝ), (1302961403/2500000000 : ℝ), (5442579703/10000000000 : ℝ)] ![(5890739009179/50000000000000 : ℝ), (42867725503859/100000000000000 : ℝ), (22675398229029/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1929557899/10000000000 : ℝ)|^4439 ≤ (5890739009179/50000000000000 : ℝ)^3415
        have hw : |(-1929557899/10000000000 : ℝ)|=(1929557899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1302961403/2500000000 : ℝ)|^4439 ≤ (42867725503859/100000000000000 : ℝ)^3415
        have hw : |(1302961403/2500000000 : ℝ)|=(1302961403/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5442579703/10000000000 : ℝ)|^4439 ≤ (22675398229029/50000000000000 : ℝ)^3415
        have hw : |(5442579703/10000000000 : ℝ)|=(5442579703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_s3_5 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323574853/2500000000 : ℝ)*x 0 + (-1817228459/10000000000 : ℝ)*x 1 + (5442579781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323574853/2500000000 : ℝ)^4439 ≤ (43751352814507/100000000000000 : ℝ)^3415 := by
    have hnat : (1323574853 : ℕ)^4439*100000000000000^3415 ≤ 43751352814507^3415*2500000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323574853 2500000000 43751352814507 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1817228459/10000000000 : ℝ)^4439 ≤ (2724462465381/25000000000000 : ℝ)^3415 := by
    have hnat : (1817228459 : ℕ)^4439*25000000000000^3415 ≤ 2724462465381^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1817228459 10000000000 2724462465381 25000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5442579781/10000000000 : ℝ)^4439 ≤ (45350797302887/100000000000000 : ℝ)^3415 := by
    have hnat : (5442579781 : ℕ)^4439*100000000000000^3415 ≤ 45350797302887^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442579781 10000000000 45350797302887 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323574853/2500000000 : ℝ), (-1817228459/10000000000 : ℝ), (5442579781/10000000000 : ℝ)] ![(43751352814507/100000000000000 : ℝ), (2724462465381/25000000000000 : ℝ), (45350797302887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323574853/2500000000 : ℝ)|^4439 ≤ (43751352814507/100000000000000 : ℝ)^3415
        have hw : |(1323574853/2500000000 : ℝ)|=(1323574853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1817228459/10000000000 : ℝ)|^4439 ≤ (2724462465381/25000000000000 : ℝ)^3415
        have hw : |(-1817228459/10000000000 : ℝ)|=(1817228459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5442579781/10000000000 : ℝ)|^4439 ≤ (45350797302887/100000000000000 : ℝ)^3415
        have hw : |(5442579781/10000000000 : ℝ)|=(5442579781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_s3_6 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294299529/10000000000 : ℝ)*x 0 + (5442579759/10000000000 : ℝ)*x 1 + (-181722833/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294299529/10000000000 : ℝ)^4439 ≤ (21875677035649/50000000000000 : ℝ)^3415 := by
    have hnat : (5294299529 : ℕ)^4439*50000000000000^3415 ≤ 21875677035649^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294299529 10000000000 21875677035649 50000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5442579759/10000000000 : ℝ)^4439 ≤ (22675398532301/50000000000000 : ℝ)^3415 := by
    have hnat : (5442579759 : ℕ)^4439*50000000000000^3415 ≤ 22675398532301^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442579759 10000000000 22675398532301 50000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (181722833/1000000000 : ℝ)^4439 ≤ (10897848855947/100000000000000 : ℝ)^3415 := by
    have hnat : (181722833 : ℕ)^4439*100000000000000^3415 ≤ 10897848855947^3415*1000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181722833 1000000000 10897848855947 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294299529/10000000000 : ℝ), (5442579759/10000000000 : ℝ), (-181722833/1000000000 : ℝ)] ![(21875677035649/50000000000000 : ℝ), (22675398532301/50000000000000 : ℝ), (10897848855947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294299529/10000000000 : ℝ)|^4439 ≤ (21875677035649/50000000000000 : ℝ)^3415
        have hw : |(5294299529/10000000000 : ℝ)|=(5294299529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5442579759/10000000000 : ℝ)|^4439 ≤ (22675398532301/50000000000000 : ℝ)^3415
        have hw : |(5442579759/10000000000 : ℝ)|=(5442579759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-181722833/1000000000 : ℝ)|^4439 ≤ (10897848855947/100000000000000 : ℝ)^3415
        have hw : |(-181722833/1000000000 : ℝ)|=(181722833/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_s3_7 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214441561/500000000 : ℝ)*x 0 + (4549585501/10000000000 : ℝ)*x 1 + (4041455473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214441561/500000000 : ℝ)^4439 ≤ (1663659625063/5000000000000 : ℝ)^3415 := by
    have hnat : (214441561 : ℕ)^4439*5000000000000^3415 ≤ 1663659625063^3415*500000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214441561 500000000 1663659625063 5000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4549585501/10000000000 : ℝ)^4439 ≤ (17963189946001/50000000000000 : ℝ)^3415 := by
    have hnat : (4549585501 : ℕ)^4439*50000000000000^3415 ≤ 17963189946001^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4549585501 10000000000 17963189946001 50000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4041455473/10000000000 : ℝ)^4439 ≤ (7700106898177/25000000000000 : ℝ)^3415 := by
    have hnat : (4041455473 : ℕ)^4439*25000000000000^3415 ≤ 7700106898177^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4041455473 10000000000 7700106898177 25000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214441561/500000000 : ℝ), (4549585501/10000000000 : ℝ), (4041455473/10000000000 : ℝ)] ![(1663659625063/5000000000000 : ℝ), (17963189946001/50000000000000 : ℝ), (7700106898177/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214441561/500000000 : ℝ)|^4439 ≤ (1663659625063/5000000000000 : ℝ)^3415
        have hw : |(214441561/500000000 : ℝ)|=(214441561/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4549585501/10000000000 : ℝ)|^4439 ≤ (17963189946001/50000000000000 : ℝ)^3415
        have hw : |(4549585501/10000000000 : ℝ)|=(4549585501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4041455473/10000000000 : ℝ)|^4439 ≤ (7700106898177/25000000000000 : ℝ)^3415
        have hw : |(4041455473/10000000000 : ℝ)|=(4041455473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1471_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160111513/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8087/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1263/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (10647/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7791/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8087/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1263/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8087/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1263/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8087/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1263/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8087/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1263/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8087/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1263/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8087/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1263/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1263/12500 : ℝ) ^ (4437/1024 : ℝ) ≤ (971609717799443/20000000000000000000 : ℝ) := by
    have hpowers : (1263/12500 : ℝ)^4437 ≤ (971609717799443/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1263 : ℕ)^4437*20000000000000000000^1024 ≤ 971609717799443^1024*12500^4437 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1263 12500 971609717799443 20000000000000000000 4437 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1263/12500 : ℝ)) (X := (971609717799443/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4437 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8087/50000 : ℝ) ^ (4437/1024 : ℝ) ≤ (37307812127072103/100000000000000000000 : ℝ) := by
    have hpowers : (8087/50000 : ℝ)^4437 ≤ (37307812127072103/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8087 : ℕ)^4437*100000000000000000000^1024 ≤ 37307812127072103^1024*50000^4437 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8087 50000 37307812127072103 100000000000000000000 4437 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8087/50000 : ℝ)) (X := (37307812127072103/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4437 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000971609717799443/10000000000000000000 : ℝ) ≤ (10000224226092837/10000000000000000 : ℝ) ^ (4437/1024 : ℝ) := by
    have hpowers : (10000971609717799443/10000000000000000000 : ℝ)^1024 ≤ (10000224226092837/10000000000000000 : ℝ)^4437 := by
      have hnat : (10000971609717799443 : ℕ)^1024*10000000000000000^4437 ≤ 10000224226092837^4437*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000971609717799443 10000000000000000000 10000224226092837 10000000000000000 1024 4437 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000224226092837/10000000000000000 : ℝ)) (X := (10000971609717799443/10000000000000000000 : ℝ)) (by norm_num) 4437 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021082930358034659/50000000000000000000 : ℝ) ≤ (10000972973649887/10000000000000000 : ℝ) ^ (4437/1024 : ℝ) := by
    have hpowers : (50021082930358034659/50000000000000000000 : ℝ)^1024 ≤ (10000972973649887/10000000000000000 : ℝ)^4437 := by
      have hnat : (50021082930358034659 : ℕ)^1024*10000000000000000^4437 ≤ 10000972973649887^4437*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021082930358034659 50000000000000000000 10000972973649887 10000000000000000 1024 4437 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000972973649887/10000000000000000 : ℝ)) (X := (50021082930358034659/50000000000000000000 : ℝ)) (by norm_num) 4437 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037307812127072103/50000000000000000000 : ℝ) ≤ (10001721721206937/10000000000000000 : ℝ) ^ (4437/1024 : ℝ) := by
    have hpowers : (50037307812127072103/50000000000000000000 : ℝ)^1024 ≤ (10001721721206937/10000000000000000 : ℝ)^4437 := by
      have hnat : (50037307812127072103 : ℕ)^1024*10000000000000000^4437 ≤ 10001721721206937^4437*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037307812127072103 50000000000000000000 10001721721206937 10000000000000000 1024 4437 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001721721206937/10000000000000000 : ℝ)) (X := (50037307812127072103/50000000000000000000 : ℝ)) (by norm_num) 4437 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(971609717799443/20000000000000000000 : ℝ) ≤ ((6068623036175065419/6070000000000000000 : ℝ)+2*(14974951141/12140000000000 : ℝ)*(1263/12500 : ℝ))^(4437/1024 : ℝ) := by
    rw [show (6068623036175065419/6070000000000000000 : ℝ)+2*(14974951141/12140000000000 : ℝ)*(1263/12500 : ℝ)=(10000224226092837/10000000000000000 : ℝ) by norm_num, show 1+2*(971609717799443/20000000000000000000 : ℝ)=(10000971609717799443/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37307812127072103/100000000000000000000 : ℝ)+(971609717799443/20000000000000000000 : ℝ) ≤ ((6068623036175065419/6070000000000000000 : ℝ)+(14974951141/12140000000000 : ℝ)*((8087/50000 : ℝ)+(1263/12500 : ℝ)))^(4437/1024 : ℝ) := by
    rw [show (6068623036175065419/6070000000000000000 : ℝ)+(14974951141/12140000000000 : ℝ)*((8087/50000 : ℝ)+(1263/12500 : ℝ))=(10000972973649887/10000000000000000 : ℝ) by norm_num, show 1+(37307812127072103/100000000000000000000 : ℝ)+(971609717799443/20000000000000000000 : ℝ)=(50021082930358034659/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37307812127072103/100000000000000000000 : ℝ) ≤ ((6068623036175065419/6070000000000000000 : ℝ)+2*(14974951141/12140000000000 : ℝ)*(8087/50000 : ℝ))^(4437/1024 : ℝ) := by
    rw [show (6068623036175065419/6070000000000000000 : ℝ)+2*(14974951141/12140000000000 : ℝ)*(8087/50000 : ℝ)=(10001721721206937/10000000000000000 : ℝ) by norm_num, show 1+2*(37307812127072103/100000000000000000000 : ℝ)=(50037307812127072103/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6068623036175065419/6070000000000000000 : ℝ)*(X 1 0+X 2 0)+(14974951141/12140000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4437/1024 : ℝ)) (lo := (1263/12500 : ℝ)) (hi := (8087/50000 : ℝ)) (c := (6068623036175065419/6070000000000000000 : ℝ)) (alpha := (14974951141/12140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6068623036175065419/6070000000000000000 : ℝ)*(X 0 1+X 2 1)+(14974951141/12140000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4437/1024 : ℝ)) (lo := (1263/12500 : ℝ)) (hi := (8087/50000 : ℝ)) (c := (6068623036175065419/6070000000000000000 : ℝ)) (alpha := (14974951141/12140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6068623036175065419/6070000000000000000 : ℝ)*(X 0 2+X 1 2)+(14974951141/12140000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4437/1024 : ℝ)) (lo := (1263/12500 : ℝ)) (hi := (8087/50000 : ℝ)) (c := (6068623036175065419/6070000000000000000 : ℝ)) (alpha := (14974951141/12140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-6029759/31250000 : ℝ)*X 0 0+(5443832749/10000000000 : ℝ)*X 0 1+(5210602091/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267755939/500000000 : ℝ)*X 1 0+(-1024603077/5000000000 : ℝ)*X 1 1+(1302650469/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1071023791/2000000000 : ℝ)*X 2 0+(2605300889/5000000000 : ℝ)*X 2 1+(-40984121/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4288754017/10000000000 : ℝ)*X 0 0+(1009674099/2500000000 : ℝ)*X 0 1+(910464729/2000000000 : ℝ)*X 0 2+(4288754017/10000000000 : ℝ)*X 1 0+(1009674099/2500000000 : ℝ)*X 1 1+(910464729/2000000000 : ℝ)*X 1 2+(4288754017/10000000000 : ℝ)*X 2 0+(1009674099/2500000000 : ℝ)*X 2 1+(910464729/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1929557899/10000000000 : ℝ)*X 0 0+(1302961403/2500000000 : ℝ)*X 0 1+(5442579703/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323574853/2500000000 : ℝ)*X 1 0+(-1817228459/10000000000 : ℝ)*X 1 1+(5442579781/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294299529/10000000000 : ℝ)*X 2 0+(5442579759/10000000000 : ℝ)*X 2 1+(-181722833/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((214441561/500000000 : ℝ)*X 0 0+(4549585501/10000000000 : ℝ)*X 0 1+(4041455473/10000000000 : ℝ)*X 0 2+(214441561/500000000 : ℝ)*X 1 0+(4549585501/10000000000 : ℝ)*X 1 1+(4041455473/10000000000 : ℝ)*X 1 2+(214441561/500000000 : ℝ)*X 2 0+(4549585501/10000000000 : ℝ)*X 2 1+(4041455473/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (222391136829994533957700599/37937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1185791697/100000000000000 : ℝ)*(base19) + (601541071/50000000000000 : ℝ)*(base23) + (32887153/50000000000000 : ℝ)*(lower2) + (81371423/100000000000000 : ℝ)*(upper3) + (53237107/50000000000000 : ℝ)*(upper5) + (779322825707407/25000000000000 : ℝ)*(major0) + (779322825707407/25000000000000 : ℝ)*(major1) + (779322825707407/25000000000000 : ℝ)*(major2) + (4287615284815049/100000000000000 : ℝ)*(sp0) + (4287631099255911/100000000000000 : ℝ)*(sp1) + (2143815540982733/50000000000000 : ℝ)*(sp2) + (973471702184077/50000000000000 : ℝ)*(sp3) + (17000232559/100000000000000 : ℝ)*(sp4) + (84010527/1250000000000 : ℝ)*(sp7) + (973475062605157/50000000000000 : ℝ)*(f.failure) + (535954035630951/12500000000000 : ℝ)*(f.sum) + (1961616625249/607000000000000000000000000 : ℝ)*base65 + (398027186996391467/151750000000000000000000000000000 : ℝ)*base68 + (1404880013809141467/151750000000000000000000000000000 : ℝ)*base70 + (169507233025141467/151750000000000000000000000000000 : ℝ)*base72 + (1413276481799/303500000000000000000000000 : ℝ)*base73 + (2209135529109141467/151750000000000000000000000000000 : ℝ)*base76 + (951940525437358533/151750000000000000000000000000000 : ℝ)*base77 + (1781422333889641467/151750000000000000000000000000000 : ℝ)*base80 + (380874231789/303500000000000000000000000 : ℝ)*base81 + (8872541/5000000000000000000000 : ℝ)*base89 + (8872541/5000000000000000000000 : ℝ)*base91 + (8872541/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (167790551277101961825239961/15175000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (193525517/12500000000000 : ℝ)*(base19) + (1949271477/100000000000000 : ℝ)*(base23) + (3763341/1562500000000 : ℝ)*(upper3) + (115853521/100000000000000 : ℝ)*(lower4) + (1365073/800000000000 : ℝ)*(upper5) + (315099567562327/10000000000000 : ℝ)*(major0) + (315099567562327/10000000000000 : ℝ)*(major1) + (315099567562327/10000000000000 : ℝ)*(major2) + (21490537377/100000000000000 : ℝ)*(sp1) + (14508519387/50000000000000 : ℝ)*(sp2) + (4333990295792787/100000000000000 : ℝ)*(sp4) + (2166983628525637/50000000000000 : ℝ)*(sp5) + (541744916185317/12500000000000 : ℝ)*(sp6) + (984000343442907/50000000000000 : ℝ)*(sp7) + (984000343442907/50000000000000 : ℝ)*(f.failure) + (4333990295792787/100000000000000 : ℝ)*(f.sum) + (3166582840901/607000000000000000000000000 : ℝ)*base65 + (346546193762229987/60700000000000000000000000000000 : ℝ)*base68 + (217163851560270013/60700000000000000000000000000000 : ℝ)*base69 + (136114677638770013/60700000000000000000000000000000 : ℝ)*base71 + (21686402443/30350000000000000000000000 : ℝ)*base74 + (364239466870770013/60700000000000000000000000000000 : ℝ)*base75 + (128879494642570013/60700000000000000000000000000000 : ℝ)*base77 + (170027295271370013/60700000000000000000000000000000 : ℝ)*base79 + (406726557347/75875000000000000000000000 : ℝ)*base81 + (31111709/5000000000000000000000 : ℝ)*base90 + (31111709/5000000000000000000000 : ℝ)*base92 + (31111709/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1471_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160111513/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8087/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1263/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10647/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7791/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1471_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1471_s4_0 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-965109709/5000000000 : ℝ)*x 0 + (1087868831/2000000000 : ℝ)*x 1 + (5214631849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (965109709/5000000000 : ℝ)^4439 ≤ (11786728522947/100000000000000 : ℝ)^3415 := by
    have hnat : (965109709 : ℕ)^4439*100000000000000^3415 ≤ 11786728522947^3415*5000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965109709 5000000000 11786728522947 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087868831/2000000000 : ℝ)^4439 ≤ (22657877438651/50000000000000 : ℝ)^3415 := by
    have hnat : (1087868831 : ℕ)^4439*50000000000000^3415 ≤ 22657877438651^3415*2000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087868831 2000000000 22657877438651 50000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5214631849/10000000000 : ℝ)^4439 ≤ (2144875829009/5000000000000 : ℝ)^3415 := by
    have hnat : (5214631849 : ℕ)^4439*5000000000000^3415 ≤ 2144875829009^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214631849 10000000000 2144875829009 5000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-965109709/5000000000 : ℝ), (1087868831/2000000000 : ℝ), (5214631849/10000000000 : ℝ)] ![(11786728522947/100000000000000 : ℝ), (22657877438651/50000000000000 : ℝ), (2144875829009/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-965109709/5000000000 : ℝ)|^4439 ≤ (11786728522947/100000000000000 : ℝ)^3415
        have hw : |(-965109709/5000000000 : ℝ)|=(965109709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1087868831/2000000000 : ℝ)|^4439 ≤ (22657877438651/50000000000000 : ℝ)^3415
        have hw : |(1087868831/2000000000 : ℝ)|=(1087868831/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5214631849/10000000000 : ℝ)|^4439 ≤ (2144875829009/5000000000000 : ℝ)^3415
        have hw : |(5214631849/10000000000 : ℝ)|=(5214631849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_s4_1 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338489067/2500000000 : ℝ)*x 0 + (-2045423351/10000000000 : ℝ)*x 1 + (1303658029/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338489067/2500000000 : ℝ)^4439 ≤ (22196627566981/50000000000000 : ℝ)^3415 := by
    have hnat : (1338489067 : ℕ)^4439*50000000000000^3415 ≤ 22196627566981^3415*2500000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338489067 2500000000 22196627566981 50000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2045423351/10000000000 : ℝ)^4439 ≤ (6354612710357/50000000000000 : ℝ)^3415 := by
    have hnat : (2045423351 : ℕ)^4439*50000000000000^3415 ≤ 6354612710357^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2045423351 10000000000 6354612710357 50000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303658029/2500000000 : ℝ)^4439 ≤ (42897519435233/100000000000000 : ℝ)^3415 := by
    have hnat : (1303658029 : ℕ)^4439*100000000000000^3415 ≤ 42897519435233^3415*2500000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303658029 2500000000 42897519435233 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338489067/2500000000 : ℝ), (-2045423351/10000000000 : ℝ), (1303658029/2500000000 : ℝ)] ![(22196627566981/50000000000000 : ℝ), (6354612710357/50000000000000 : ℝ), (42897519435233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338489067/2500000000 : ℝ)|^4439 ≤ (22196627566981/50000000000000 : ℝ)^3415
        have hw : |(1338489067/2500000000 : ℝ)|=(1338489067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2045423351/10000000000 : ℝ)|^4439 ≤ (6354612710357/50000000000000 : ℝ)^3415
        have hw : |(-2045423351/10000000000 : ℝ)|=(2045423351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1303658029/2500000000 : ℝ)|^4439 ≤ (42897519435233/100000000000000 : ℝ)^3415
        have hw : |(1303658029/2500000000 : ℝ)|=(1303658029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_s4_2 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (13384891/25000000 : ℝ)*x 0 + (5214631881/10000000000 : ℝ)*x 1 + (-409084697/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13384891/25000000 : ℝ)^4439 ≤ (44393256556653/100000000000000 : ℝ)^3415 := by
    have hnat : (13384891 : ℕ)^4439*100000000000000^3415 ≤ 44393256556653^3415*25000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13384891 25000000 44393256556653 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5214631881/10000000000 : ℝ)^4439 ≤ (21448758461179/50000000000000 : ℝ)^3415 := by
    have hnat : (5214631881 : ℕ)^4439*50000000000000^3415 ≤ 21448758461179^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214631881 10000000000 21448758461179 50000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (409084697/2000000000 : ℝ)^4439 ≤ (12709226502983/100000000000000 : ℝ)^3415 := by
    have hnat : (409084697 : ℕ)^4439*100000000000000^3415 ≤ 12709226502983^3415*2000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409084697 2000000000 12709226502983 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13384891/25000000 : ℝ), (5214631881/10000000000 : ℝ), (-409084697/2000000000 : ℝ)] ![(44393256556653/100000000000000 : ℝ), (21448758461179/50000000000000 : ℝ), (12709226502983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13384891/25000000 : ℝ)|^4439 ≤ (44393256556653/100000000000000 : ℝ)^3415
        have hw : |(13384891/25000000 : ℝ)|=(13384891/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5214631881/10000000000 : ℝ)|^4439 ≤ (21448758461179/50000000000000 : ℝ)^3415
        have hw : |(5214631881/10000000000 : ℝ)|=(5214631881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-409084697/2000000000 : ℝ)|^4439 ≤ (12709226502983/100000000000000 : ℝ)^3415
        have hw : |(-409084697/2000000000 : ℝ)|=(409084697/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_s4_3 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1072296793/2500000000 : ℝ)*x 0 + (404802487/1000000000 : ℝ)*x 1 + (4542892569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072296793/2500000000 : ℝ)^4439 ≤ (33276782107367/100000000000000 : ℝ)^3415 := by
    have hnat : (1072296793 : ℕ)^4439*100000000000000^3415 ≤ 33276782107367^3415*2500000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072296793 2500000000 33276782107367 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (404802487/1000000000 : ℝ)^4439 ≤ (30865522150283/100000000000000 : ℝ)^3415 := by
    have hnat : (404802487 : ℕ)^4439*100000000000000^3415 ≤ 30865522150283^3415*1000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404802487 1000000000 30865522150283 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4542892569/10000000000 : ℝ)^4439 ≤ (1120552991357/3125000000000 : ℝ)^3415 := by
    have hnat : (4542892569 : ℕ)^4439*3125000000000^3415 ≤ 1120552991357^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4542892569 10000000000 1120552991357 3125000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072296793/2500000000 : ℝ), (404802487/1000000000 : ℝ), (4542892569/10000000000 : ℝ)] ![(33276782107367/100000000000000 : ℝ), (30865522150283/100000000000000 : ℝ), (1120552991357/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072296793/2500000000 : ℝ)|^4439 ≤ (33276782107367/100000000000000 : ℝ)^3415
        have hw : |(1072296793/2500000000 : ℝ)|=(1072296793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(404802487/1000000000 : ℝ)|^4439 ≤ (30865522150283/100000000000000 : ℝ)^3415
        have hw : |(404802487/1000000000 : ℝ)|=(404802487/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4542892569/10000000000 : ℝ)|^4439 ≤ (1120552991357/3125000000000 : ℝ)^3415
        have hw : |(4542892569/10000000000 : ℝ)|=(4542892569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_s4_4 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-38605011/200000000 : ℝ)*x 0 + (1303946731/2500000000 : ℝ)*x 1 + (5438180707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (38605011/200000000 : ℝ)^4439 ≤ (5893487816129/50000000000000 : ℝ)^3415 := by
    have hnat : (38605011 : ℕ)^4439*50000000000000^3415 ≤ 5893487816129^3415*200000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38605011 200000000 5893487816129 50000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1303946731/2500000000 : ℝ)^4439 ≤ (42909868303107/100000000000000 : ℝ)^3415 := by
    have hnat : (1303946731 : ℕ)^4439*100000000000000^3415 ≤ 42909868303107^3415*2500000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303946731 2500000000 42909868303107 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5438180707/10000000000 : ℝ)^4439 ≤ (22651578024359/50000000000000 : ℝ)^3415 := by
    have hnat : (5438180707 : ℕ)^4439*50000000000000^3415 ≤ 22651578024359^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438180707 10000000000 22651578024359 50000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-38605011/200000000 : ℝ), (1303946731/2500000000 : ℝ), (5438180707/10000000000 : ℝ)] ![(5893487816129/50000000000000 : ℝ), (42909868303107/100000000000000 : ℝ), (22651578024359/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-38605011/200000000 : ℝ)|^4439 ≤ (5893487816129/50000000000000 : ℝ)^3415
        have hw : |(-38605011/200000000 : ℝ)|=(38605011/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1303946731/2500000000 : ℝ)|^4439 ≤ (42909868303107/100000000000000 : ℝ)^3415
        have hw : |(1303946731/2500000000 : ℝ)|=(1303946731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5438180707/10000000000 : ℝ)|^4439 ≤ (22651578024359/50000000000000 : ℝ)^3415
        have hw : |(5438180707/10000000000 : ℝ)|=(5438180707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_s4_5 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323840311/2500000000 : ℝ)*x 0 + (-910937239/5000000000 : ℝ)*x 1 + (2719090563/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323840311/2500000000 : ℝ)^4439 ≤ (43762759153963/100000000000000 : ℝ)^3415 := by
    have hnat : (1323840311 : ℕ)^4439*100000000000000^3415 ≤ 43762759153963^3415*2500000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323840311 2500000000 43762759153963 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (910937239/5000000000 : ℝ)^4439 ≤ (2733520063693/25000000000000 : ℝ)^3415 := by
    have hnat : (910937239 : ℕ)^4439*25000000000000^3415 ≤ 2733520063693^3415*5000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      910937239 5000000000 2733520063693 25000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2719090563/5000000000 : ℝ)^4439 ≤ (45303160585869/100000000000000 : ℝ)^3415 := by
    have hnat : (2719090563 : ℕ)^4439*100000000000000^3415 ≤ 45303160585869^3415*5000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719090563 5000000000 45303160585869 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323840311/2500000000 : ℝ), (-910937239/5000000000 : ℝ), (2719090563/5000000000 : ℝ)] ![(43762759153963/100000000000000 : ℝ), (2733520063693/25000000000000 : ℝ), (45303160585869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323840311/2500000000 : ℝ)|^4439 ≤ (43762759153963/100000000000000 : ℝ)^3415
        have hw : |(1323840311/2500000000 : ℝ)|=(1323840311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-910937239/5000000000 : ℝ)|^4439 ≤ (2733520063693/25000000000000 : ℝ)^3415
        have hw : |(-910937239/5000000000 : ℝ)|=(910937239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2719090563/5000000000 : ℝ)|^4439 ≤ (45303160585869/100000000000000 : ℝ)^3415
        have hw : |(2719090563/5000000000 : ℝ)|=(2719090563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_s4_6 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647680717/5000000000 : ℝ)*x 0 + (271909057/500000000 : ℝ)*x 1 + (-1821874197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647680717/5000000000 : ℝ)^4439 ≤ (43762761195029/100000000000000 : ℝ)^3415 := by
    have hnat : (2647680717 : ℕ)^4439*100000000000000^3415 ≤ 43762761195029^3415*5000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647680717 5000000000 43762761195029 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271909057/500000000 : ℝ)^4439 ≤ (45303160737469/100000000000000 : ℝ)^3415 := by
    have hnat : (271909057 : ℕ)^4439*100000000000000^3415 ≤ 45303160737469^3415*500000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271909057 500000000 45303160737469 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1821874197/10000000000 : ℝ)^4439 ≤ (10934078062651/100000000000000 : ℝ)^3415 := by
    have hnat : (1821874197 : ℕ)^4439*100000000000000^3415 ≤ 10934078062651^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1821874197 10000000000 10934078062651 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647680717/5000000000 : ℝ), (271909057/500000000 : ℝ), (-1821874197/10000000000 : ℝ)] ![(43762761195029/100000000000000 : ℝ), (45303160737469/100000000000000 : ℝ), (10934078062651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647680717/5000000000 : ℝ)|^4439 ≤ (43762761195029/100000000000000 : ℝ)^3415
        have hw : |(2647680717/5000000000 : ℝ)|=(2647680717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271909057/500000000 : ℝ)|^4439 ≤ (45303160737469/100000000000000 : ℝ)^3415
        have hw : |(271909057/500000000 : ℝ)|=(271909057/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1821874197/10000000000 : ℝ)|^4439 ≤ (10934078062651/100000000000000 : ℝ)^3415
        have hw : |(-1821874197/10000000000 : ℝ)|=(1821874197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_s4_7 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4289256209/10000000000 : ℝ)*x 0 + (2270174919/5000000000 : ℝ)*x 1 + (2025293183/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4289256209/10000000000 : ℝ)^4439 ≤ (33277478322919/100000000000000 : ℝ)^3415 := by
    have hnat : (4289256209 : ℕ)^4439*100000000000000^3415 ≤ 33277478322919^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4289256209 10000000000 33277478322919 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2270174919/5000000000 : ℝ)^4439 ≤ (7166321934773/20000000000000 : ℝ)^3415 := by
    have hnat : (2270174919 : ℕ)^4439*20000000000000^3415 ≤ 7166321934773^3415*5000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2270174919 5000000000 7166321934773 20000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2025293183/5000000000 : ℝ)^4439 ≤ (30890911978871/100000000000000 : ℝ)^3415 := by
    have hnat : (2025293183 : ℕ)^4439*100000000000000^3415 ≤ 30890911978871^3415*5000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025293183 5000000000 30890911978871 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4289256209/10000000000 : ℝ), (2270174919/5000000000 : ℝ), (2025293183/5000000000 : ℝ)] ![(33277478322919/100000000000000 : ℝ), (7166321934773/20000000000000 : ℝ), (30890911978871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4289256209/10000000000 : ℝ)|^4439 ≤ (33277478322919/100000000000000 : ℝ)^3415
        have hw : |(4289256209/10000000000 : ℝ)|=(4289256209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2270174919/5000000000 : ℝ)|^4439 ≤ (7166321934773/20000000000000 : ℝ)^3415
        have hw : |(2270174919/5000000000 : ℝ)|=(2270174919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2025293183/5000000000 : ℝ)|^4439 ≤ (30890911978871/100000000000000 : ℝ)^3415
        have hw : |(2025293183/5000000000 : ℝ)|=(2025293183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1471_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160111513/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7791/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10647/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10733/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (484/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7791/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10647/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7791/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10647/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7791/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10647/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7791/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10647/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7791/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10647/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7791/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10647/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10647/100000 : ℝ) ^ (4437/1024 : ℝ) ≤ (6094921157910593/100000000000000000000 : ℝ) := by
    have hpowers : (10647/100000 : ℝ)^4437 ≤ (6094921157910593/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10647 : ℕ)^4437*100000000000000000000^1024 ≤ 6094921157910593^1024*100000^4437 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10647 100000 6094921157910593 100000000000000000000 4437 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10647/100000 : ℝ)) (X := (6094921157910593/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4437 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7791/50000 : ℝ) ^ (4437/1024 : ℝ) ≤ (3967710995665859/12500000000000000000 : ℝ) := by
    have hpowers : (7791/50000 : ℝ)^4437 ≤ (3967710995665859/12500000000000000000 : ℝ)^1024 := by
      have hnat : (7791 : ℕ)^4437*12500000000000000000^1024 ≤ 3967710995665859^1024*50000^4437 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7791 50000 3967710995665859 12500000000000000000 4437 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7791/50000 : ℝ)) (X := (3967710995665859/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4437 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006094921157910593/50000000000000000000 : ℝ) ≤ (10000281311998237/10000000000000000 : ℝ) ^ (4437/1024 : ℝ) := by
    have hpowers : (50006094921157910593/50000000000000000000 : ℝ)^1024 ≤ (10000281311998237/10000000000000000 : ℝ)^4437 := by
      have hnat : (50006094921157910593 : ℕ)^1024*10000000000000000^4437 ≤ 10000281311998237^4437*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006094921157910593 50000000000000000000 10000281311998237 10000000000000000 1024 4437 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000281311998237/10000000000000000 : ℝ)) (X := (50006094921157910593/50000000000000000000 : ℝ)) (by norm_num) 4437 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007567321824647493/20000000000000000000 : ℝ) ≤ (125010913638379/125000000000000 : ℝ) ^ (4437/1024 : ℝ) := by
    have hpowers : (20007567321824647493/20000000000000000000 : ℝ)^1024 ≤ (125010913638379/125000000000000 : ℝ)^4437 := by
      have hnat : (20007567321824647493 : ℕ)^1024*125000000000000^4437 ≤ 125010913638379^4437*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007567321824647493 20000000000000000000 125010913638379 125000000000000 1024 4437 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125010913638379/125000000000000 : ℝ)) (X := (20007567321824647493/20000000000000000000 : ℝ)) (by norm_num) 4437 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253967710995665859/6250000000000000000 : ℝ) ≤ (10001464870142403/10000000000000000 : ℝ) ^ (4437/1024 : ℝ) := by
    have hpowers : (6253967710995665859/6250000000000000000 : ℝ)^1024 ≤ (10001464870142403/10000000000000000 : ℝ)^4437 := by
      have hnat : (6253967710995665859 : ℕ)^1024*10000000000000000^4437 ≤ 10001464870142403^4437*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253967710995665859 6250000000000000000 10001464870142403 10000000000000000 1024 4437 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001464870142403/10000000000000000 : ℝ)) (X := (6253967710995665859/6250000000000000000 : ℝ)) (by norm_num) 4437 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6094921157910593/100000000000000000000 : ℝ) ≤ ((2349466044340493533/2350000000000000000 : ℝ)+2*(591779072083/493500000000000 : ℝ)*(10647/100000 : ℝ))^(4437/1024 : ℝ) := by
    rw [show (2349466044340493533/2350000000000000000 : ℝ)+2*(591779072083/493500000000000 : ℝ)*(10647/100000 : ℝ)=(10000281311998237/10000000000000000 : ℝ) by norm_num, show 1+2*(6094921157910593/100000000000000000000 : ℝ)=(50006094921157910593/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3967710995665859/12500000000000000000 : ℝ)+(6094921157910593/100000000000000000000 : ℝ) ≤ ((2349466044340493533/2350000000000000000 : ℝ)+(591779072083/493500000000000 : ℝ)*((7791/50000 : ℝ)+(10647/100000 : ℝ)))^(4437/1024 : ℝ) := by
    rw [show (2349466044340493533/2350000000000000000 : ℝ)+(591779072083/493500000000000 : ℝ)*((7791/50000 : ℝ)+(10647/100000 : ℝ))=(125010913638379/125000000000000 : ℝ) by norm_num, show 1+(3967710995665859/12500000000000000000 : ℝ)+(6094921157910593/100000000000000000000 : ℝ)=(20007567321824647493/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3967710995665859/12500000000000000000 : ℝ) ≤ ((2349466044340493533/2350000000000000000 : ℝ)+2*(591779072083/493500000000000 : ℝ)*(7791/50000 : ℝ))^(4437/1024 : ℝ) := by
    rw [show (2349466044340493533/2350000000000000000 : ℝ)+2*(591779072083/493500000000000 : ℝ)*(7791/50000 : ℝ)=(10001464870142403/10000000000000000 : ℝ) by norm_num, show 1+2*(3967710995665859/12500000000000000000 : ℝ)=(6253967710995665859/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2349466044340493533/2350000000000000000 : ℝ)*(X 1 0+X 2 0)+(591779072083/493500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4437/1024 : ℝ)) (lo := (10647/100000 : ℝ)) (hi := (7791/50000 : ℝ)) (c := (2349466044340493533/2350000000000000000 : ℝ)) (alpha := (591779072083/493500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2349466044340493533/2350000000000000000 : ℝ)*(X 0 1+X 2 1)+(591779072083/493500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4437/1024 : ℝ)) (lo := (10647/100000 : ℝ)) (hi := (7791/50000 : ℝ)) (c := (2349466044340493533/2350000000000000000 : ℝ)) (alpha := (591779072083/493500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2349466044340493533/2350000000000000000 : ℝ)*(X 0 2+X 1 2)+(591779072083/493500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4437/1024 : ℝ)) (lo := (10647/100000 : ℝ)) (hi := (7791/50000 : ℝ)) (c := (2349466044340493533/2350000000000000000 : ℝ)) (alpha := (591779072083/493500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-965109709/5000000000 : ℝ)*X 0 0+(1087868831/2000000000 : ℝ)*X 0 1+(5214631849/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338489067/2500000000 : ℝ)*X 1 0+(-2045423351/10000000000 : ℝ)*X 1 1+(1303658029/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((13384891/25000000 : ℝ)*X 2 0+(5214631881/10000000000 : ℝ)*X 2 1+(-409084697/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1072296793/2500000000 : ℝ)*X 0 0+(404802487/1000000000 : ℝ)*X 0 1+(4542892569/10000000000 : ℝ)*X 0 2+(1072296793/2500000000 : ℝ)*X 1 0+(404802487/1000000000 : ℝ)*X 1 1+(4542892569/10000000000 : ℝ)*X 1 2+(1072296793/2500000000 : ℝ)*X 2 0+(404802487/1000000000 : ℝ)*X 2 1+(4542892569/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-38605011/200000000 : ℝ)*X 0 0+(1303946731/2500000000 : ℝ)*X 0 1+(5438180707/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323840311/2500000000 : ℝ)*X 1 0+(-910937239/5000000000 : ℝ)*X 1 1+(2719090563/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647680717/5000000000 : ℝ)*X 2 0+(271909057/500000000 : ℝ)*X 2 1+(-1821874197/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4289256209/10000000000 : ℝ)*X 0 0+(2270174919/5000000000 : ℝ)*X 0 1+(2025293183/5000000000 : ℝ)*X 0 2+(4289256209/10000000000 : ℝ)*X 1 0+(2270174919/5000000000 : ℝ)*X 1 1+(2025293183/5000000000 : ℝ)*X 1 2+(4289256209/10000000000 : ℝ)*X 2 0+(2270174919/5000000000 : ℝ)*X 2 1+(2025293183/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (365465503737693665249331819/41125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (80948113/5000000000000 : ℝ)*(base19) + (315967343/20000000000000 : ℝ)*(base23) + (1992253/2500000000000 : ℝ)*(lower2) + (81841189/25000000000000 : ℝ)*(upper3) + (111234127/100000000000000 : ℝ)*(upper5) + (161773854555561/5000000000000 : ℝ)*(major0) + (161773854555561/5000000000000 : ℝ)*(major1) + (161773854555561/5000000000000 : ℝ)*(major2) + (2225081880718489/50000000000000 : ℝ)*(sp0) + (4450187469747601/100000000000000 : ℝ)*(sp1) + (2225093754436573/50000000000000 : ℝ)*(sp2) + (505187972122127/25000000000000 : ℝ)*(sp3) + (6331818221/25000000000000 : ℝ)*(sp4) + (2581760151/20000000000000 : ℝ)*(sp7) + (1010382398644631/50000000000000 : ℝ)*(f.failure) + (4450189088709861/100000000000000 : ℝ)*(f.sum) + (5826191076631/1645000000000000000000000000 : ℝ)*base66 + (1636887866886090909/82250000000000000000000000000000 : ℝ)*base68 + (1086364816697090909/82250000000000000000000000000000 : ℝ)*base70 + (767827472937840909/82250000000000000000000000000000 : ℝ)*base72 + (8161035861771/1645000000000000000000000000 : ℝ)*base74 + (791119592090590909/82250000000000000000000000000000 : ℝ)*base76 + (1431002752494840909/82250000000000000000000000000000 : ℝ)*base78 + (640366213731090909/82250000000000000000000000000000 : ℝ)*base80 + (84860912991/102812500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (18736703/5000000000000000000000 : ℝ)*base89 + (18736703/5000000000000000000000 : ℝ)*base91 + (18736703/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (368466718616930056642589661/58750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2113379/400000000000 : ℝ)*(base19) + (580908477/50000000000000 : ℝ)*(base23) + (108348703/50000000000000 : ℝ)*(upper3) + (32103687/20000000000000 : ℝ)*(lower4) + (11850511/50000000000000 : ℝ)*(upper5) + (1634581502873739/50000000000000 : ℝ)*(major0) + (1634581502873739/50000000000000 : ℝ)*(major1) + (1634581502873739/50000000000000 : ℝ)*(major2) + (951595223/10000000000000 : ℝ)*(sp1) + (991572083/4000000000000 : ℝ)*(sp2) + (1124130492946173/25000000000000 : ℝ)*(sp4) + (140515997733991/3125000000000 : ℝ)*(sp5) + (2248248010332831/50000000000000 : ℝ)*(sp6) + (255225478831391/12500000000000 : ℝ)*(sp7) + (255225478831391/12500000000000 : ℝ)*(f.failure) + (1124130492946173/25000000000000 : ℝ)*(f.sum) + (1764721843597/587500000000000000000000000 : ℝ)*base65 + (280230771875270113/117500000000000000000000000000000 : ℝ)*base68 + (719524898725270113/117500000000000000000000000000000 : ℝ)*base70 + (2018275484729887/117500000000000000000000000000000 : ℝ)*base71 + (74955806759/73437500000000000000000000 : ℝ)*base73 + (541254503615270113/117500000000000000000000000000000 : ℝ)*base76 + (389761732465270113/117500000000000000000000000000000 : ℝ)*base78 + (1142517937352229887/117500000000000000000000000000000 : ℝ)*base79 + (678340478531/1175000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (9904583/1250000000000000000000 : ℝ)*base89 + (9904583/1250000000000000000000 : ℝ)*base91 + (9904583/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1471_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160111513/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7791/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10647/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10733/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (484/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1471_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1471_s5_0 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1930322661/10000000000 : ℝ)*x 0 + (5438706817/10000000000 : ℝ)*x 1 + (1303800161/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1930322661/10000000000 : ℝ)^4439 ≤ (2357509603147/20000000000000 : ℝ)^3415 := by
    have hnat : (1930322661 : ℕ)^4439*20000000000000^3415 ≤ 2357509603147^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1930322661 10000000000 2357509603147 20000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438706817/10000000000 : ℝ)^4439 ≤ (4530885312607/10000000000000 : ℝ)^3415 := by
    have hnat : (5438706817 : ℕ)^4439*10000000000000^3415 ≤ 4530885312607^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438706817 10000000000 4530885312607 10000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303800161/2500000000 : ℝ)^4439 ≤ (42903598851747/100000000000000 : ℝ)^3415 := by
    have hnat : (1303800161 : ℕ)^4439*100000000000000^3415 ≤ 42903598851747^3415*2500000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303800161 2500000000 42903598851747 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1930322661/10000000000 : ℝ), (5438706817/10000000000 : ℝ), (1303800161/2500000000 : ℝ)] ![(2357509603147/20000000000000 : ℝ), (4530885312607/10000000000000 : ℝ), (42903598851747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1930322661/10000000000 : ℝ)|^4439 ≤ (2357509603147/20000000000000 : ℝ)^3415
        have hw : |(-1930322661/10000000000 : ℝ)|=(1930322661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438706817/10000000000 : ℝ)|^4439 ≤ (4530885312607/10000000000000 : ℝ)^3415
        have hw : |(5438706817/10000000000 : ℝ)|=(5438706817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1303800161/2500000000 : ℝ)|^4439 ≤ (42903598851747/100000000000000 : ℝ)^3415
        have hw : |(1303800161/2500000000 : ℝ)|=(1303800161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_s5_1 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535378451/1000000000 : ℝ)*x 0 + (-2044895077/10000000000 : ℝ)*x 1 + (40743783/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535378451/1000000000 : ℝ)^4439 ≤ (22195701970919/50000000000000 : ℝ)^3415 := by
    have hnat : (535378451 : ℕ)^4439*50000000000000^3415 ≤ 22195701970919^3415*1000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535378451 1000000000 22195701970919 50000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2044895077/10000000000 : ℝ)^4439 ≤ (12704958911099/100000000000000 : ℝ)^3415 := by
    have hnat : (2044895077 : ℕ)^4439*100000000000000^3415 ≤ 12704958911099^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2044895077 10000000000 12704958911099 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40743783/78125000 : ℝ)^4439 ≤ (42903637134239/100000000000000 : ℝ)^3415 := by
    have hnat : (40743783 : ℕ)^4439*100000000000000^3415 ≤ 42903637134239^3415*78125000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40743783 78125000 42903637134239 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535378451/1000000000 : ℝ), (-2044895077/10000000000 : ℝ), (40743783/78125000 : ℝ)] ![(22195701970919/50000000000000 : ℝ), (12704958911099/100000000000000 : ℝ), (42903637134239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535378451/1000000000 : ℝ)|^4439 ≤ (22195701970919/50000000000000 : ℝ)^3415
        have hw : |(535378451/1000000000 : ℝ)|=(535378451/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2044895077/10000000000 : ℝ)|^4439 ≤ (12704958911099/100000000000000 : ℝ)^3415
        have hw : |(-2044895077/10000000000 : ℝ)|=(2044895077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(40743783/78125000 : ℝ)|^4439 ≤ (42903637134239/100000000000000 : ℝ)^3415
        have hw : |(40743783/78125000 : ℝ)|=(40743783/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_s5_2 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133844723/250000000 : ℝ)*x 0 + (1303801089/2500000000 : ℝ)*x 1 + (-255611127/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133844723/250000000 : ℝ)^4439 ≤ (8878290294439/20000000000000 : ℝ)^3415 := by
    have hnat : (133844723 : ℕ)^4439*20000000000000^3415 ≤ 8878290294439^3415*250000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133844723 250000000 8878290294439 20000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1303801089/2500000000 : ℝ)^4439 ≤ (42903638545773/100000000000000 : ℝ)^3415 := by
    have hnat : (1303801089 : ℕ)^4439*100000000000000^3415 ≤ 42903638545773^3415*2500000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303801089 2500000000 42903638545773 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (255611127/1250000000 : ℝ)^4439 ≤ (3176227490611/25000000000000 : ℝ)^3415 := by
    have hnat : (255611127 : ℕ)^4439*25000000000000^3415 ≤ 3176227490611^3415*1250000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255611127 1250000000 3176227490611 25000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133844723/250000000 : ℝ), (1303801089/2500000000 : ℝ), (-255611127/1250000000 : ℝ)] ![(8878290294439/20000000000000 : ℝ), (42903638545773/100000000000000 : ℝ), (3176227490611/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133844723/250000000 : ℝ)|^4439 ≤ (8878290294439/20000000000000 : ℝ)^3415
        have hw : |(133844723/250000000 : ℝ)|=(133844723/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1303801089/2500000000 : ℝ)|^4439 ≤ (42903638545773/100000000000000 : ℝ)^3415
        have hw : |(1303801089/2500000000 : ℝ)|=(1303801089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-255611127/1250000000 : ℝ)|^4439 ≤ (3176227490611/25000000000000 : ℝ)^3415
        have hw : |(-255611127/1250000000 : ℝ)|=(255611127/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_s5_3 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1072312919/2500000000 : ℝ)*x 0 + (4049344903/10000000000 : ℝ)*x 1 + (1135388471/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072312919/2500000000 : ℝ)^4439 ≤ (6655486521799/20000000000000 : ℝ)^3415 := by
    have hnat : (1072312919 : ℕ)^4439*20000000000000^3415 ≤ 6655486521799^3415*2500000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072312919 2500000000 6655486521799 20000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4049344903/10000000000 : ℝ)^4439 ≤ (30878605860369/100000000000000 : ℝ)^3415 := by
    have hnat : (4049344903 : ℕ)^4439*100000000000000^3415 ≤ 30878605860369^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4049344903 10000000000 30878605860369 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1135388471/2500000000 : ℝ)^4439 ≤ (8960990379363/25000000000000 : ℝ)^3415 := by
    have hnat : (1135388471 : ℕ)^4439*25000000000000^3415 ≤ 8960990379363^3415*2500000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135388471 2500000000 8960990379363 25000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072312919/2500000000 : ℝ), (4049344903/10000000000 : ℝ), (1135388471/2500000000 : ℝ)] ![(6655486521799/20000000000000 : ℝ), (30878605860369/100000000000000 : ℝ), (8960990379363/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072312919/2500000000 : ℝ)|^4439 ≤ (6655486521799/20000000000000 : ℝ)^3415
        have hw : |(1072312919/2500000000 : ℝ)|=(1072312919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4049344903/10000000000 : ℝ)|^4439 ≤ (30878605860369/100000000000000 : ℝ)^3415
        have hw : |(4049344903/10000000000 : ℝ)|=(4049344903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1135388471/2500000000 : ℝ)|^4439 ≤ (8960990379363/25000000000000 : ℝ)^3415
        have hw : |(1135388471/2500000000 : ℝ)|=(1135388471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_s5_4 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1930349539/10000000000 : ℝ)*x 0 + (5216344383/10000000000 : ℝ)*x 1 + (1359389401/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1930349539/10000000000 : ℝ)^4439 ≤ (14734701703/125000000000 : ℝ)^3415 := by
    have hnat : (1930349539 : ℕ)^4439*125000000000^3415 ≤ 14734701703^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1930349539 10000000000 14734701703 125000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216344383/10000000000 : ℝ)^4439 ≤ (42915829749839/100000000000000 : ℝ)^3415 := by
    have hnat : (5216344383 : ℕ)^4439*100000000000000^3415 ≤ 42915829749839^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216344383 10000000000 42915829749839 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1359389401/2500000000 : ℝ)^4439 ≤ (22648204439443/50000000000000 : ℝ)^3415 := by
    have hnat : (1359389401 : ℕ)^4439*50000000000000^3415 ≤ 22648204439443^3415*2500000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359389401 2500000000 22648204439443 50000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1930349539/10000000000 : ℝ), (5216344383/10000000000 : ℝ), (1359389401/2500000000 : ℝ)] ![(14734701703/125000000000 : ℝ), (42915829749839/100000000000000 : ℝ), (22648204439443/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1930349539/10000000000 : ℝ)|^4439 ≤ (14734701703/125000000000 : ℝ)^3415
        have hw : |(-1930349539/10000000000 : ℝ)|=(1930349539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216344383/10000000000 : ℝ)|^4439 ≤ (42915829749839/100000000000000 : ℝ)^3415
        have hw : |(5216344383/10000000000 : ℝ)|=(5216344383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1359389401/2500000000 : ℝ)|^4439 ≤ (22648204439443/50000000000000 : ℝ)^3415
        have hw : |(1359389401/2500000000 : ℝ)|=(1359389401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_s5_5 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295511007/10000000000 : ℝ)*x 0 + (-364506771/2000000000 : ℝ)*x 1 + (1359389371/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295511007/10000000000 : ℝ)^4439 ≤ (43764367983061/100000000000000 : ℝ)^3415 := by
    have hnat : (5295511007 : ℕ)^4439*100000000000000^3415 ≤ 43764367983061^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295511007 10000000000 43764367983061 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (364506771/2000000000 : ℝ)^4439 ≤ (5469612214087/50000000000000 : ℝ)^3415 := by
    have hnat : (364506771 : ℕ)^4439*50000000000000^3415 ≤ 5469612214087^3415*2000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      364506771 2000000000 5469612214087 50000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1359389371/2500000000 : ℝ)^4439 ≤ (45296407579507/100000000000000 : ℝ)^3415 := by
    have hnat : (1359389371 : ℕ)^4439*100000000000000^3415 ≤ 45296407579507^3415*2500000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359389371 2500000000 45296407579507 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295511007/10000000000 : ℝ), (-364506771/2000000000 : ℝ), (1359389371/2500000000 : ℝ)] ![(43764367983061/100000000000000 : ℝ), (5469612214087/50000000000000 : ℝ), (45296407579507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295511007/10000000000 : ℝ)|^4439 ≤ (43764367983061/100000000000000 : ℝ)^3415
        have hw : |(5295511007/10000000000 : ℝ)|=(5295511007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-364506771/2000000000 : ℝ)|^4439 ≤ (5469612214087/50000000000000 : ℝ)^3415
        have hw : |(-364506771/2000000000 : ℝ)|=(364506771/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1359389371/2500000000 : ℝ)|^4439 ≤ (45296407579507/100000000000000 : ℝ)^3415
        have hw : |(1359389371/2500000000 : ℝ)|=(1359389371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_s5_6 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295510991/10000000000 : ℝ)*x 0 + (5437557543/10000000000 : ℝ)*x 1 + (-911266897/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295510991/10000000000 : ℝ)^4439 ≤ (2188218390559/5000000000000 : ℝ)^3415 := by
    have hnat : (5295510991 : ℕ)^4439*5000000000000^3415 ≤ 2188218390559^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295510991 10000000000 2188218390559 5000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437557543/10000000000 : ℝ)^4439 ≤ (176939094603/390625000000 : ℝ)^3415 := by
    have hnat : (5437557543 : ℕ)^4439*390625000000^3415 ≤ 176939094603^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437557543 10000000000 176939094603 390625000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (911266897/5000000000 : ℝ)^4439 ≤ (2734805988063/25000000000000 : ℝ)^3415 := by
    have hnat : (911266897 : ℕ)^4439*25000000000000^3415 ≤ 2734805988063^3415*5000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      911266897 5000000000 2734805988063 25000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295510991/10000000000 : ℝ), (5437557543/10000000000 : ℝ), (-911266897/5000000000 : ℝ)] ![(2188218390559/5000000000000 : ℝ), (176939094603/390625000000 : ℝ), (2734805988063/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295510991/10000000000 : ℝ)|^4439 ≤ (2188218390559/5000000000000 : ℝ)^3415
        have hw : |(5295510991/10000000000 : ℝ)|=(5295510991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437557543/10000000000 : ℝ)|^4439 ≤ (176939094603/390625000000 : ℝ)^3415
        have hw : |(5437557543/10000000000 : ℝ)|=(5437557543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-911266897/5000000000 : ℝ)|^4439 ≤ (2734805988063/25000000000000 : ℝ)^3415
        have hw : |(-911266897/5000000000 : ℝ)|=(911266897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_s5_7 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (857862971/2000000000 : ℝ)*x 0 + (2269521071/5000000000 : ℝ)*x 1 + (4051879813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (857862971/2000000000 : ℝ)^4439 ≤ (33278069751277/100000000000000 : ℝ)^3415 := by
    have hnat : (857862971 : ℕ)^4439*100000000000000^3415 ≤ 33278069751277^3415*2000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857862971 2000000000 33278069751277 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2269521071/5000000000 : ℝ)^4439 ≤ (35818195637517/100000000000000 : ℝ)^3415 := by
    have hnat : (2269521071 : ℕ)^4439*100000000000000^3415 ≤ 35818195637517^3415*5000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2269521071 5000000000 35818195637517 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4051879813/10000000000 : ℝ)^4439 ≤ (30903734596687/100000000000000 : ℝ)^3415 := by
    have hnat : (4051879813 : ℕ)^4439*100000000000000^3415 ≤ 30903734596687^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4051879813 10000000000 30903734596687 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(857862971/2000000000 : ℝ), (2269521071/5000000000 : ℝ), (4051879813/10000000000 : ℝ)] ![(33278069751277/100000000000000 : ℝ), (35818195637517/100000000000000 : ℝ), (30903734596687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(857862971/2000000000 : ℝ)|^4439 ≤ (33278069751277/100000000000000 : ℝ)^3415
        have hw : |(857862971/2000000000 : ℝ)|=(857862971/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2269521071/5000000000 : ℝ)|^4439 ≤ (35818195637517/100000000000000 : ℝ)^3415
        have hw : |(2269521071/5000000000 : ℝ)|=(2269521071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4051879813/10000000000 : ℝ)|^4439 ≤ (30903734596687/100000000000000 : ℝ)^3415
        have hw : |(4051879813/10000000000 : ℝ)|=(4051879813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1471_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160111513/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10733/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2149/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (619/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10733/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10733/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10733/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10733/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10733/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10733/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10733/100000 : ℝ) ^ (4437/1024 : ℝ) ≤ (6311129345089147/100000000000000000000 : ℝ) := by
    have hpowers : (10733/100000 : ℝ)^4437 ≤ (6311129345089147/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10733 : ℕ)^4437*100000000000000000000^1024 ≤ 6311129345089147^1024*100000^4437 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10733 100000 6311129345089147 100000000000000000000 4437 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10733/100000 : ℝ)) (X := (6311129345089147/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4437 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (484/3125 : ℝ) ^ (4437/1024 : ℝ) ≤ (15460142202341059/50000000000000000000 : ℝ) := by
    have hpowers : (484/3125 : ℝ)^4437 ≤ (15460142202341059/50000000000000000000 : ℝ)^1024 := by
      have hnat : (484 : ℕ)^4437*50000000000000000000^1024 ≤ 15460142202341059^1024*3125^4437 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        484 3125 15460142202341059 50000000000000000000 4437 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (484/3125 : ℝ)) (X := (15460142202341059/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4437 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006311129345089147/50000000000000000000 : ℝ) ≤ (10000291290635077/10000000000000000 : ℝ) ^ (4437/1024 : ℝ) := by
    have hpowers : (50006311129345089147/50000000000000000000 : ℝ)^1024 ≤ (10000291290635077/10000000000000000 : ℝ)^4437 := by
      have hnat : (50006311129345089147 : ℕ)^1024*10000000000000000^4437 ≤ 10000291290635077^4437*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006311129345089147 50000000000000000000 10000291290635077 10000000000000000 1024 4437 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000291290635077/10000000000000000 : ℝ)) (X := (50006311129345089147/50000000000000000000 : ℝ)) (by norm_num) 4437 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007446282749954253/20000000000000000000 : ℝ) ≤ (1250107391000653/1250000000000000 : ℝ) ^ (4437/1024 : ℝ) := by
    have hpowers : (20007446282749954253/20000000000000000000 : ℝ)^1024 ≤ (1250107391000653/1250000000000000 : ℝ)^4437 := by
      have hnat : (20007446282749954253 : ℕ)^1024*1250000000000000^4437 ≤ 1250107391000653^4437*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007446282749954253 20000000000000000000 1250107391000653 1250000000000000 1024 4437 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250107391000653/1250000000000000 : ℝ)) (X := (20007446282749954253/20000000000000000000 : ℝ)) (by norm_num) 4437 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015460142202341059/25000000000000000000 : ℝ) ≤ (10001426965375371/10000000000000000 : ℝ) ^ (4437/1024 : ℝ) := by
    have hpowers : (25015460142202341059/25000000000000000000 : ℝ)^1024 ≤ (10001426965375371/10000000000000000 : ℝ)^4437 := by
      have hnat : (25015460142202341059 : ℕ)^1024*10000000000000000^4437 ≤ 10001426965375371^4437*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015460142202341059 25000000000000000000 10001426965375371 10000000000000000 1024 4437 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001426965375371/10000000000000000 : ℝ)) (X := (25015460142202341059/25000000000000000000 : ℝ)) (by norm_num) 4437 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6311129345089147/100000000000000000000 : ℝ) ≤ ((47539195889982215633/47550000000000000000 : ℝ)+2*(567837370147/475500000000000 : ℝ)*(10733/100000 : ℝ))^(4437/1024 : ℝ) := by
    rw [show (47539195889982215633/47550000000000000000 : ℝ)+2*(567837370147/475500000000000 : ℝ)*(10733/100000 : ℝ)=(10000291290635077/10000000000000000 : ℝ) by norm_num, show 1+2*(6311129345089147/100000000000000000000 : ℝ)=(50006311129345089147/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15460142202341059/50000000000000000000 : ℝ)+(6311129345089147/100000000000000000000 : ℝ) ≤ ((47539195889982215633/47550000000000000000 : ℝ)+(567837370147/475500000000000 : ℝ)*((484/3125 : ℝ)+(10733/100000 : ℝ)))^(4437/1024 : ℝ) := by
    rw [show (47539195889982215633/47550000000000000000 : ℝ)+(567837370147/475500000000000 : ℝ)*((484/3125 : ℝ)+(10733/100000 : ℝ))=(1250107391000653/1250000000000000 : ℝ) by norm_num, show 1+(15460142202341059/50000000000000000000 : ℝ)+(6311129345089147/100000000000000000000 : ℝ)=(20007446282749954253/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15460142202341059/50000000000000000000 : ℝ) ≤ ((47539195889982215633/47550000000000000000 : ℝ)+2*(567837370147/475500000000000 : ℝ)*(484/3125 : ℝ))^(4437/1024 : ℝ) := by
    rw [show (47539195889982215633/47550000000000000000 : ℝ)+2*(567837370147/475500000000000 : ℝ)*(484/3125 : ℝ)=(10001426965375371/10000000000000000 : ℝ) by norm_num, show 1+2*(15460142202341059/50000000000000000000 : ℝ)=(25015460142202341059/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (47539195889982215633/47550000000000000000 : ℝ)*(X 1 0+X 2 0)+(567837370147/475500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4437/1024 : ℝ)) (lo := (10733/100000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (47539195889982215633/47550000000000000000 : ℝ)) (alpha := (567837370147/475500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (47539195889982215633/47550000000000000000 : ℝ)*(X 0 1+X 2 1)+(567837370147/475500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4437/1024 : ℝ)) (lo := (10733/100000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (47539195889982215633/47550000000000000000 : ℝ)) (alpha := (567837370147/475500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (47539195889982215633/47550000000000000000 : ℝ)*(X 0 2+X 1 2)+(567837370147/475500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4437/1024 : ℝ)) (lo := (10733/100000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (47539195889982215633/47550000000000000000 : ℝ)) (alpha := (567837370147/475500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1930322661/10000000000 : ℝ)*X 0 0+(5438706817/10000000000 : ℝ)*X 0 1+(1303800161/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((535378451/1000000000 : ℝ)*X 1 0+(-2044895077/10000000000 : ℝ)*X 1 1+(40743783/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((133844723/250000000 : ℝ)*X 2 0+(1303801089/2500000000 : ℝ)*X 2 1+(-255611127/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1072312919/2500000000 : ℝ)*X 0 0+(4049344903/10000000000 : ℝ)*X 0 1+(1135388471/2500000000 : ℝ)*X 0 2+(1072312919/2500000000 : ℝ)*X 1 0+(4049344903/10000000000 : ℝ)*X 1 1+(1135388471/2500000000 : ℝ)*X 1 2+(1072312919/2500000000 : ℝ)*X 2 0+(4049344903/10000000000 : ℝ)*X 2 1+(1135388471/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1930349539/10000000000 : ℝ)*X 0 0+(5216344383/10000000000 : ℝ)*X 0 1+(1359389401/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295511007/10000000000 : ℝ)*X 1 0+(-364506771/2000000000 : ℝ)*X 1 1+(1359389371/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295510991/10000000000 : ℝ)*X 2 0+(5437557543/10000000000 : ℝ)*X 2 1+(-911266897/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((857862971/2000000000 : ℝ)*X 0 0+(2269521071/5000000000 : ℝ)*X 0 1+(4051879813/10000000000 : ℝ)*X 0 2+(857862971/2000000000 : ℝ)*X 1 0+(2269521071/5000000000 : ℝ)*X 1 1+(4051879813/10000000000 : ℝ)*X 1 2+(857862971/2000000000 : ℝ)*X 2 0+(2269521071/5000000000 : ℝ)*X 2 1+(4051879813/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11082874510714177300014160667/792500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (77504747/6250000000000 : ℝ)*(base23) + (388683971/100000000000000 : ℝ)*(lower2) + (64333883/20000000000000 : ℝ)*(upper3) + (1114630129/100000000000000 : ℝ)*(upper4) + (3103369119/100000000000000 : ℝ)*(upper5) + (3252935459112967/100000000000000 : ℝ)*(major0) + (3252935459112967/100000000000000 : ℝ)*(major1) + (3252935459112967/100000000000000 : ℝ)*(major2) + (2237055448387167/50000000000000 : ℝ)*(sp0) + (2237084232790759/50000000000000 : ℝ)*(sp1) + (279637533389413/6250000000000 : ℝ)*(sp2) + (507917169440677/25000000000000 : ℝ)*(sp3) + (45438766113/50000000000000 : ℝ)*(sp4) + (16654362521/50000000000000 : ℝ)*(sp5) + (507917169440677/25000000000000 : ℝ)*(f.failure) + (3495470136177/78125000000 : ℝ)*(f.sum) + (107156851620649/23775000000000000000000000000 : ℝ)*base65 + (9366400995771771037/1585000000000000000000000000000000 : ℝ)*base67 + (10558991907251771037/1585000000000000000000000000000000 : ℝ)*base69 + (43223707530401771037/1585000000000000000000000000000000 : ℝ)*base71 + (48375030267949/23775000000000000000000000000 : ℝ)*base73 + (5052022322651771037/1585000000000000000000000000000000 : ℝ)*base75 + (9024099311091771037/1585000000000000000000000000000000 : ℝ)*base77 + (5693786381751771037/1585000000000000000000000000000000 : ℝ)*base79 + (36881230927451/23775000000000000000000000000 : ℝ)*base82 + (16785699/2500000000000000000000 : ℝ)*base90 + (16785699/2500000000000000000000 : ℝ)*base92 + (16785699/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3212807736212857156725767769/396250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (369454109/25000000000000 : ℝ)*(base19) + (1575393117/100000000000000 : ℝ)*(base23) + (162624937/100000000000000 : ℝ)*(upper3) + (46547073/100000000000000 : ℝ)*(lower4) + (183138199/100000000000000 : ℝ)*(upper5) + (1643307249278393/50000000000000 : ℝ)*(major0) + (1643307249278393/50000000000000 : ℝ)*(major1) + (1643307249278393/50000000000000 : ℝ)*(major2) + (20569701223/100000000000000 : ℝ)*(sp1) + (5672149907/25000000000000 : ℝ)*(sp2) + (904105061944759/20000000000000 : ℝ)*(sp4) + (565062907775767/12500000000000 : ℝ)*(sp5) + (4520501045731049/100000000000000 : ℝ)*(sp6) + (128293963570127/6250000000000 : ℝ)*(sp7) + (128293963570127/6250000000000 : ℝ)*(f.failure) + (904105061944759/20000000000000 : ℝ)*(f.sum) + (110298570239917/23775000000000000000000000000 : ℝ)*base65 + (1570980785998894077/792500000000000000000000000000000 : ℝ)*base68 + (8696555260846394077/792500000000000000000000000000000 : ℝ)*base70 + (3705608698605923/792500000000000000000000000000000 : ℝ)*base71 + (34871093231467/23775000000000000000000000000 : ℝ)*base73 + (14341612483176394077/792500000000000000000000000000000 : ℝ)*base76 + (7125296801123894077/792500000000000000000000000000000 : ℝ)*base78 + (5089871802176105923/792500000000000000000000000000000 : ℝ)*base79 + (11216971773373/5943750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (3072151/625000000000000000000 : ℝ)*base89 + (3072151/625000000000000000000 : ℝ)*base91 + (3072151/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1471_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160111513/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10733/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2149/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (619/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1471_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1471_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160111513/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8087/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1263/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2149/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (619/4000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1471_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1471_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1471_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160111513/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8087/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1263/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2149/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (619/4000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1471_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
