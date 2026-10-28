-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1129_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:26:37.524494+00:00
-- url     : https://prove2.me/submissions/c9949561-a2be-474e-a14a-72885e938a13

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
theorem support_rectangle_w1129_s6_0 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-543270943/2500000000 : ℝ)*x 0 + (674205713/1250000000 : ℝ)*x 1 + (1053034441/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543270943/2500000000 : ℝ)^4161 ≤ (3300810973889/25000000000000 : ℝ)^3137 := by
    have hnat : (543270943 : ℕ)^4161*25000000000000^3137 ≤ 3300810973889^3137*2500000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543270943 2500000000 3300810973889 25000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674205713/1250000000 : ℝ)^4161 ≤ (44092195519087/100000000000000 : ℝ)^3137 := by
    have hnat : (674205713 : ℕ)^4161*100000000000000^3137 ≤ 44092195519087^3137*1250000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674205713 1250000000 44092195519087 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053034441/2000000000 : ℝ)^4161 ≤ (21352280285399/50000000000000 : ℝ)^3137 := by
    have hnat : (1053034441 : ℕ)^4161*50000000000000^3137 ≤ 21352280285399^3137*2000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053034441 2000000000 21352280285399 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-543270943/2500000000 : ℝ), (674205713/1250000000 : ℝ), (1053034441/2000000000 : ℝ)] ![(3300810973889/25000000000000 : ℝ), (44092195519087/100000000000000 : ℝ), (21352280285399/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-543270943/2500000000 : ℝ)|^4161 ≤ (3300810973889/25000000000000 : ℝ)^3137
        have hw : |(-543270943/2500000000 : ℝ)|=(543270943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674205713/1250000000 : ℝ)|^4161 ≤ (44092195519087/100000000000000 : ℝ)^3137
        have hw : |(674205713/1250000000 : ℝ)|=(674205713/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053034441/2000000000 : ℝ)|^4161 ≤ (21352280285399/50000000000000 : ℝ)^3137
        have hw : |(1053034441/2000000000 : ℝ)|=(1053034441/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s6_1 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336224929/2500000000 : ℝ)*x 0 + (-2238256377/10000000000 : ℝ)*x 1 + (26325861/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336224929/2500000000 : ℝ)^4161 ≤ (43564408152851/100000000000000 : ℝ)^3137 := by
    have hnat : (1336224929 : ℕ)^4161*100000000000000^3137 ≤ 43564408152851^3137*2500000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336224929 2500000000 43564408152851 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2238256377/10000000000 : ℝ)^4161 ≤ (13731031308629/100000000000000 : ℝ)^3137 := by
    have hnat : (2238256377 : ℕ)^4161*100000000000000^3137 ≤ 13731031308629^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238256377 10000000000 13731031308629 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26325861/50000000 : ℝ)^4161 ≤ (21352280258503/50000000000000 : ℝ)^3137 := by
    have hnat : (26325861 : ℕ)^4161*50000000000000^3137 ≤ 21352280258503^3137*50000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26325861 50000000 21352280258503 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336224929/2500000000 : ℝ), (-2238256377/10000000000 : ℝ), (26325861/50000000 : ℝ)] ![(43564408152851/100000000000000 : ℝ), (13731031308629/100000000000000 : ℝ), (21352280258503/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336224929/2500000000 : ℝ)|^4161 ≤ (43564408152851/100000000000000 : ℝ)^3137
        have hw : |(1336224929/2500000000 : ℝ)|=(1336224929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2238256377/10000000000 : ℝ)|^4161 ≤ (13731031308629/100000000000000 : ℝ)^3137
        have hw : |(-2238256377/10000000000 : ℝ)|=(2238256377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(26325861/50000000 : ℝ)|^4161 ≤ (21352280258503/50000000000000 : ℝ)^3137
        have hw : |(26325861/50000000 : ℝ)|=(26325861/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s6_2 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344899703/10000000000 : ℝ)*x 0 + (5265172217/10000000000 : ℝ)*x 1 + (-559564093/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344899703/10000000000 : ℝ)^4161 ≤ (2722775500769/6250000000000 : ℝ)^3137 := by
    have hnat : (5344899703 : ℕ)^4161*6250000000000^3137 ≤ 2722775500769^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344899703 10000000000 2722775500769 6250000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265172217/10000000000 : ℝ)^4161 ≤ (21352280349949/50000000000000 : ℝ)^3137 := by
    have hnat : (5265172217 : ℕ)^4161*50000000000000^3137 ≤ 21352280349949^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265172217 10000000000 21352280349949 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (559564093/2500000000 : ℝ)^4161 ≤ (13731031267943/100000000000000 : ℝ)^3137 := by
    have hnat : (559564093 : ℕ)^4161*100000000000000^3137 ≤ 13731031267943^3137*2500000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559564093 2500000000 13731031267943 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344899703/10000000000 : ℝ), (5265172217/10000000000 : ℝ), (-559564093/2500000000 : ℝ)] ![(2722775500769/6250000000000 : ℝ), (21352280349949/50000000000000 : ℝ), (13731031267943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344899703/10000000000 : ℝ)|^4161 ≤ (2722775500769/6250000000000 : ℝ)^3137
        have hw : |(5344899703/10000000000 : ℝ)|=(5344899703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265172217/10000000000 : ℝ)|^4161 ≤ (21352280349949/50000000000000 : ℝ)^3137
        have hw : |(5265172217/10000000000 : ℝ)|=(5265172217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-559564093/2500000000 : ℝ)|^4161 ≤ (13731031267943/100000000000000 : ℝ)^3137
        have hw : |(-559564093/2500000000 : ℝ)|=(559564093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s6_3 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4366489081/10000000000 : ℝ)*x 0 + (4240874657/10000000000 : ℝ)*x 1 + (1123954443/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4366489081/10000000000 : ℝ)^4161 ≤ (33316704918139/100000000000000 : ℝ)^3137 := by
    have hnat : (4366489081 : ℕ)^4161*100000000000000^3137 ≤ 33316704918139^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366489081 10000000000 33316704918139 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4240874657/10000000000 : ℝ)^4161 ≤ (3205140046747/10000000000000 : ℝ)^3137 := by
    have hnat : (4240874657 : ℕ)^4161*10000000000000^3137 ≤ 3205140046747^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4240874657 10000000000 3205140046747 10000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1123954443/2500000000 : ℝ)^4161 ≤ (17315947301341/50000000000000 : ℝ)^3137 := by
    have hnat : (1123954443 : ℕ)^4161*50000000000000^3137 ≤ 17315947301341^3137*2500000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123954443 2500000000 17315947301341 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4366489081/10000000000 : ℝ), (4240874657/10000000000 : ℝ), (1123954443/2500000000 : ℝ)] ![(33316704918139/100000000000000 : ℝ), (3205140046747/10000000000000 : ℝ), (17315947301341/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4366489081/10000000000 : ℝ)|^4161 ≤ (33316704918139/100000000000000 : ℝ)^3137
        have hw : |(4366489081/10000000000 : ℝ)|=(4366489081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4240874657/10000000000 : ℝ)|^4161 ≤ (3205140046747/10000000000000 : ℝ)^3137
        have hw : |(4240874657/10000000000 : ℝ)|=(4240874657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1123954443/2500000000 : ℝ)|^4161 ≤ (17315947301341/50000000000000 : ℝ)^3137
        have hw : |(1123954443/2500000000 : ℝ)|=(1123954443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s6_4 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1086544417/5000000000 : ℝ)*x 0 + (5265496609/10000000000 : ℝ)*x 1 + (2696660037/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086544417/5000000000 : ℝ)^4161 ≤ (6601642345407/50000000000000 : ℝ)^3137 := by
    have hnat : (1086544417 : ℕ)^4161*50000000000000^3137 ≤ 6601642345407^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086544417 5000000000 6601642345407 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265496609/10000000000 : ℝ)^4161 ≤ (21354025325641/50000000000000 : ℝ)^3137 := by
    have hnat : (5265496609 : ℕ)^4161*50000000000000^3137 ≤ 21354025325641^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265496609 10000000000 21354025325641 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696660037/5000000000 : ℝ)^4161 ≤ (44088664641703/100000000000000 : ℝ)^3137 := by
    have hnat : (2696660037 : ℕ)^4161*100000000000000^3137 ≤ 44088664641703^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696660037 5000000000 44088664641703 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1086544417/5000000000 : ℝ), (5265496609/10000000000 : ℝ), (2696660037/5000000000 : ℝ)] ![(6601642345407/50000000000000 : ℝ), (21354025325641/50000000000000 : ℝ), (44088664641703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1086544417/5000000000 : ℝ)|^4161 ≤ (6601642345407/50000000000000 : ℝ)^3137
        have hw : |(-1086544417/5000000000 : ℝ)|=(1086544417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265496609/10000000000 : ℝ)|^4161 ≤ (21354025325641/50000000000000 : ℝ)^3137
        have hw : |(5265496609/10000000000 : ℝ)|=(5265496609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696660037/5000000000 : ℝ)|^4161 ≤ (44088664641703/100000000000000 : ℝ)^3137
        have hw : |(2696660037/5000000000 : ℝ)|=(2696660037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s6_5 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312381917/10000000000 : ℝ)*x 0 + (-2110108537/10000000000 : ℝ)*x 1 + (1348330013/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312381917/10000000000 : ℝ)^4161 ≤ (5401650004059/12500000000000 : ℝ)^3137 := by
    have hnat : (5312381917 : ℕ)^4161*12500000000000^3137 ≤ 5401650004059^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312381917 10000000000 5401650004059 12500000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2110108537/10000000000 : ℝ)^4161 ≤ (6349067772387/50000000000000 : ℝ)^3137 := by
    have hnat : (2110108537 : ℕ)^4161*50000000000000^3137 ≤ 6349067772387^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110108537 10000000000 6349067772387 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348330013/2500000000 : ℝ)^4161 ≤ (22044332201577/50000000000000 : ℝ)^3137 := by
    have hnat : (1348330013 : ℕ)^4161*50000000000000^3137 ≤ 22044332201577^3137*2500000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348330013 2500000000 22044332201577 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312381917/10000000000 : ℝ), (-2110108537/10000000000 : ℝ), (1348330013/2500000000 : ℝ)] ![(5401650004059/12500000000000 : ℝ), (6349067772387/50000000000000 : ℝ), (22044332201577/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312381917/10000000000 : ℝ)|^4161 ≤ (5401650004059/12500000000000 : ℝ)^3137
        have hw : |(5312381917/10000000000 : ℝ)|=(5312381917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2110108537/10000000000 : ℝ)|^4161 ≤ (6349067772387/50000000000000 : ℝ)^3137
        have hw : |(-2110108537/10000000000 : ℝ)|=(2110108537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348330013/2500000000 : ℝ)|^4161 ≤ (22044332201577/50000000000000 : ℝ)^3137
        have hw : |(1348330013/2500000000 : ℝ)|=(1348330013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s6_6 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312381987/10000000000 : ℝ)*x 0 + (2696659957/5000000000 : ℝ)*x 1 + (-2110108631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312381987/10000000000 : ℝ)^4161 ≤ (43213200787753/100000000000000 : ℝ)^3137 := by
    have hnat : (5312381987 : ℕ)^4161*100000000000000^3137 ≤ 43213200787753^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312381987 10000000000 43213200787753 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696659957/5000000000 : ℝ)^4161 ≤ (8817732581361/20000000000000 : ℝ)^3137 := by
    have hnat : (2696659957 : ℕ)^4161*20000000000000^3137 ≤ 8817732581361^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696659957 5000000000 8817732581361 20000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2110108631/10000000000 : ℝ)^4161 ≤ (12698136295093/100000000000000 : ℝ)^3137 := by
    have hnat : (2110108631 : ℕ)^4161*100000000000000^3137 ≤ 12698136295093^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110108631 10000000000 12698136295093 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312381987/10000000000 : ℝ), (2696659957/5000000000 : ℝ), (-2110108631/10000000000 : ℝ)] ![(43213200787753/100000000000000 : ℝ), (8817732581361/20000000000000 : ℝ), (12698136295093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312381987/10000000000 : ℝ)|^4161 ≤ (43213200787753/100000000000000 : ℝ)^3137
        have hw : |(5312381987/10000000000 : ℝ)|=(5312381987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696659957/5000000000 : ℝ)|^4161 ≤ (8817732581361/20000000000000 : ℝ)^3137
        have hw : |(2696659957/5000000000 : ℝ)|=(2696659957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2110108631/10000000000 : ℝ)|^4161 ≤ (12698136295093/100000000000000 : ℝ)^3137
        have hw : |(-2110108631/10000000000 : ℝ)|=(2110108631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s6_7 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2183249493/5000000000 : ℝ)*x 0 + (4495173893/10000000000 : ℝ)*x 1 + (1060380223/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183249493/5000000000 : ℝ)^4161 ≤ (16658402582121/50000000000000 : ℝ)^3137 := by
    have hnat : (2183249493 : ℕ)^4161*50000000000000^3137 ≤ 16658402582121^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183249493 5000000000 16658402582121 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4495173893/10000000000 : ℝ)^4161 ≤ (34625315830351/100000000000000 : ℝ)^3137 := by
    have hnat : (4495173893 : ℕ)^4161*100000000000000^3137 ≤ 34625315830351^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495173893 10000000000 34625315830351 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1060380223/2500000000 : ℝ)^4161 ≤ (16028939495551/50000000000000 : ℝ)^3137 := by
    have hnat : (1060380223 : ℕ)^4161*50000000000000^3137 ≤ 16028939495551^3137*2500000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060380223 2500000000 16028939495551 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2183249493/5000000000 : ℝ), (4495173893/10000000000 : ℝ), (1060380223/2500000000 : ℝ)] ![(16658402582121/50000000000000 : ℝ), (34625315830351/100000000000000 : ℝ), (16028939495551/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2183249493/5000000000 : ℝ)|^4161 ≤ (16658402582121/50000000000000 : ℝ)^3137
        have hw : |(2183249493/5000000000 : ℝ)|=(2183249493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4495173893/10000000000 : ℝ)|^4161 ≤ (34625315830351/100000000000000 : ℝ)^3137
        have hw : |(4495173893/10000000000 : ℝ)|=(4495173893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1060380223/2500000000 : ℝ)|^4161 ≤ (16028939495551/50000000000000 : ℝ)^3137
        have hw : |(1060380223/2500000000 : ℝ)|=(1060380223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1129_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193761/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (353/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (354/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (281/2000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3521/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (353/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3521/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (353/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3521/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (353/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3521/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (353/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3521/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (353/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3521/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (353/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (353/3125 : ℝ) ^ (8321/2048 : ℝ) ≤ (2838403176041889/20000000000000000000 : ℝ) := by
    have hpowers : (353/3125 : ℝ)^8321 ≤ (2838403176041889/20000000000000000000 : ℝ)^2048 := by
      have hnat : (353 : ℕ)^8321*20000000000000000000^2048 ≤ 2838403176041889^2048*3125^8321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        353 3125 2838403176041889 20000000000000000000 8321 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (353/3125 : ℝ)) (X := (2838403176041889/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3521/25000 : ℝ) ^ (8321/2048 : ℝ) ≤ (34776332576629927/100000000000000000000 : ℝ) := by
    have hpowers : (3521/25000 : ℝ)^8321 ≤ (34776332576629927/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3521 : ℕ)^8321*100000000000000000000^2048 ≤ 34776332576629927^2048*25000^8321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3521 25000 34776332576629927 100000000000000000000 8321 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3521/25000 : ℝ)) (X := (34776332576629927/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002838403176041889/10000000000000000000 : ℝ) ≤ (10000698525161469/10000000000000000 : ℝ) ^ (8321/2048 : ℝ) := by
    have hpowers : (10002838403176041889/10000000000000000000 : ℝ)^2048 ≤ (10000698525161469/10000000000000000 : ℝ)^8321 := by
      have hnat : (10002838403176041889 : ℕ)^2048*10000000000000000^8321 ≤ 10000698525161469^8321*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002838403176041889 10000000000000000000 10000698525161469 10000000000000000 2048 8321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000698525161469/10000000000000000 : ℝ)) (X := (10002838403176041889/10000000000000000000 : ℝ)) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012242087114209843/25000000000000000000 : ℝ) ≤ (5000602503736961/5000000000000000 : ℝ) ^ (8321/2048 : ℝ) := by
    have hpowers : (25012242087114209843/25000000000000000000 : ℝ)^2048 ≤ (5000602503736961/5000000000000000 : ℝ)^8321 := by
      have hnat : (25012242087114209843 : ℕ)^2048*5000000000000000^8321 ≤ 5000602503736961^8321*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012242087114209843 25000000000000000000 5000602503736961 5000000000000000 2048 8321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000602503736961/5000000000000000 : ℝ)) (X := (25012242087114209843/25000000000000000000 : ℝ)) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034776332576629927/50000000000000000000 : ℝ) ≤ (80013691918291/80000000000000 : ℝ) ^ (8321/2048 : ℝ) := by
    have hpowers : (50034776332576629927/50000000000000000000 : ℝ)^2048 ≤ (80013691918291/80000000000000 : ℝ)^8321 := by
      have hnat : (50034776332576629927 : ℕ)^2048*80000000000000^8321 ≤ 80013691918291^8321*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034776332576629927 50000000000000000000 80013691918291 80000000000000 2048 8321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80013691918291/80000000000000 : ℝ)) (X := (50034776332576629927/50000000000000000000 : ℝ)) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2838403176041889/20000000000000000000 : ℝ) ≤ ((169942103900897789/170000000000000000 : ℝ)+2*(12353227133/6800000000000 : ℝ)*(353/3125 : ℝ))^(8321/2048 : ℝ) := by
    rw [show (169942103900897789/170000000000000000 : ℝ)+2*(12353227133/6800000000000 : ℝ)*(353/3125 : ℝ)=(10000698525161469/10000000000000000 : ℝ) by norm_num, show 1+2*(2838403176041889/20000000000000000000 : ℝ)=(10002838403176041889/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34776332576629927/100000000000000000000 : ℝ)+(2838403176041889/20000000000000000000 : ℝ) ≤ ((169942103900897789/170000000000000000 : ℝ)+(12353227133/6800000000000 : ℝ)*((3521/25000 : ℝ)+(353/3125 : ℝ)))^(8321/2048 : ℝ) := by
    rw [show (169942103900897789/170000000000000000 : ℝ)+(12353227133/6800000000000 : ℝ)*((3521/25000 : ℝ)+(353/3125 : ℝ))=(5000602503736961/5000000000000000 : ℝ) by norm_num, show 1+(34776332576629927/100000000000000000000 : ℝ)+(2838403176041889/20000000000000000000 : ℝ)=(25012242087114209843/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34776332576629927/100000000000000000000 : ℝ) ≤ ((169942103900897789/170000000000000000 : ℝ)+2*(12353227133/6800000000000 : ℝ)*(3521/25000 : ℝ))^(8321/2048 : ℝ) := by
    rw [show (169942103900897789/170000000000000000 : ℝ)+2*(12353227133/6800000000000 : ℝ)*(3521/25000 : ℝ)=(80013691918291/80000000000000 : ℝ) by norm_num, show 1+2*(34776332576629927/100000000000000000000 : ℝ)=(50034776332576629927/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (169942103900897789/170000000000000000 : ℝ)*(X 1 0+X 2 0)+(12353227133/6800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8321/2048 : ℝ)) (lo := (353/3125 : ℝ)) (hi := (3521/25000 : ℝ)) (c := (169942103900897789/170000000000000000 : ℝ)) (alpha := (12353227133/6800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (169942103900897789/170000000000000000 : ℝ)*(X 0 1+X 2 1)+(12353227133/6800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8321/2048 : ℝ)) (lo := (353/3125 : ℝ)) (hi := (3521/25000 : ℝ)) (c := (169942103900897789/170000000000000000 : ℝ)) (alpha := (12353227133/6800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (169942103900897789/170000000000000000 : ℝ)*(X 0 2+X 1 2)+(12353227133/6800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8321/2048 : ℝ)) (lo := (353/3125 : ℝ)) (hi := (3521/25000 : ℝ)) (c := (169942103900897789/170000000000000000 : ℝ)) (alpha := (12353227133/6800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-543270943/2500000000 : ℝ)*X 0 0+(674205713/1250000000 : ℝ)*X 0 1+(1053034441/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336224929/2500000000 : ℝ)*X 1 0+(-2238256377/10000000000 : ℝ)*X 1 1+(26325861/50000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344899703/10000000000 : ℝ)*X 2 0+(5265172217/10000000000 : ℝ)*X 2 1+(-559564093/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4366489081/10000000000 : ℝ)*X 0 0+(4240874657/10000000000 : ℝ)*X 0 1+(1123954443/2500000000 : ℝ)*X 0 2+(4366489081/10000000000 : ℝ)*X 1 0+(4240874657/10000000000 : ℝ)*X 1 1+(1123954443/2500000000 : ℝ)*X 1 2+(4366489081/10000000000 : ℝ)*X 2 0+(4240874657/10000000000 : ℝ)*X 2 1+(1123954443/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1086544417/5000000000 : ℝ)*X 0 0+(5265496609/10000000000 : ℝ)*X 0 1+(2696660037/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312381917/10000000000 : ℝ)*X 1 0+(-2110108537/10000000000 : ℝ)*X 1 1+(1348330013/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312381987/10000000000 : ℝ)*X 2 0+(2696659957/5000000000 : ℝ)*X 2 1+(-2110108631/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2183249493/5000000000 : ℝ)*X 0 0+(4495173893/10000000000 : ℝ)*X 0 1+(1060380223/2500000000 : ℝ)*X 0 2+(2183249493/5000000000 : ℝ)*X 1 0+(4495173893/10000000000 : ℝ)*X 1 1+(1060380223/2500000000 : ℝ)*X 1 2+(2183249493/5000000000 : ℝ)*X 2 0+(4495173893/10000000000 : ℝ)*X 2 1+(1060380223/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (41799485056567056383709669/4250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2046159601/100000000000000 : ℝ)*(base19) + (467646997/25000000000000 : ℝ)*(base23) + (83722301/100000000000000 : ℝ)*(lower2) + (254927739/100000000000000 : ℝ)*(upper3) + (8960629/6250000000000 : ℝ)*(upper5) + (2926580348911693/50000000000000 : ℝ)*(major0) + (2926580348911693/50000000000000 : ℝ)*(major1) + (2926580348911693/50000000000000 : ℝ)*(major2) + (972970599410961/12500000000000 : ℝ)*(sp0) + (486488634625299/6250000000000 : ℝ)*(sp1) + (7783818329576397/100000000000000 : ℝ)*(sp2) + (1961235341975419/50000000000000 : ℝ)*(sp3) + (27702438349/50000000000000 : ℝ)*(sp4) + (30183692441/100000000000000 : ℝ)*(sp7) + (49031260845541/1250000000000 : ℝ)*(f.failure) + (1556764040032877/20000000000000 : ℝ)*(f.sum) + (83774742049/170000000000000000000000000 : ℝ)*base65 + (29557914976328223/8500000000000000000000000000000 : ℝ)*base68 + (5007732934171777/8500000000000000000000000000000 : ℝ)*base69 + (53298034526171777/8500000000000000000000000000000 : ℝ)*base71 + (124426438299/170000000000000000000000000 : ℝ)*base73 + (134809047516171777/8500000000000000000000000000000 : ℝ)*base75 + (84205349823328223/8500000000000000000000000000000 : ℝ)*base78 + (126366486946171777/8500000000000000000000000000000 : ℝ)*base79 + (556843400089/170000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (9701/1000000000000000000 : ℝ)*base89 + (9701/1000000000000000000 : ℝ)*base91 + (9701/1000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9347605627968641965115061/1062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (374033151/20000000000000 : ℝ)*(base19) + (985521793/50000000000000 : ℝ)*(base23) + (82536659/50000000000000 : ℝ)*(upper3) + (5264437/25000000000000 : ℝ)*(lower4) + (233851973/100000000000000 : ℝ)*(upper5) + (1470710720308117/25000000000000 : ℝ)*(major0) + (1470710720308117/25000000000000 : ℝ)*(major1) + (1470710720308117/25000000000000 : ℝ)*(major2) + (26502236811/50000000000000 : ℝ)*(sp1) + (4616814233/10000000000000 : ℝ)*(sp2) + (7823293059850087/100000000000000 : ℝ)*(sp4) + (782323818521071/10000000000000 : ℝ)*(sp5) + (782324492066417/10000000000000 : ℝ)*(sp6) + (1971196204678313/50000000000000 : ℝ)*(sp7) + (1971196204678313/50000000000000 : ℝ)*(f.failure) + (7823293059850087/100000000000000 : ℝ)*(f.sum) + (353214439069/85000000000000000000000000 : ℝ)*base66 + (8921309463828313/4250000000000000000000000000000 : ℝ)*base67 + (67250192940578313/4250000000000000000000000000000 : ℝ)*base69 + (27026378921578313/4250000000000000000000000000000 : ℝ)*base71 + (121112893029/85000000000000000000000000 : ℝ)*base74 + (5080687692078313/4250000000000000000000000000000 : ℝ)*base75 + (2158419349921687/4250000000000000000000000000000 : ℝ)*base78 + (62309503434078313/4250000000000000000000000000000 : ℝ)*base79 + (497210587791/85000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (405193/40000000000000000000 : ℝ)*base89 + (405193/40000000000000000000 : ℝ)*base91 + (405193/40000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1129_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193761/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (353/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (354/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (281/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1129_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1129_s7_0 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2173114883/10000000000 : ℝ)*x 0 + (539330453/1000000000 : ℝ)*x 1 + (2632746381/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173114883/10000000000 : ℝ)^4161 ≤ (13203494623281/100000000000000 : ℝ)^3137 := by
    have hnat : (2173114883 : ℕ)^4161*100000000000000^3137 ≤ 13203494623281^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173114883 10000000000 13203494623281 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539330453/1000000000 : ℝ)^4161 ≤ (688882751507/1562500000000 : ℝ)^3137 := by
    have hnat : (539330453 : ℕ)^4161*1562500000000^3137 ≤ 688882751507^3137*1000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539330453 1000000000 688882751507 1562500000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632746381/5000000000 : ℝ)^4161 ≤ (21354004631579/50000000000000 : ℝ)^3137 := by
    have hnat : (2632746381 : ℕ)^4161*50000000000000^3137 ≤ 21354004631579^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632746381 5000000000 21354004631579 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2173114883/10000000000 : ℝ), (539330453/1000000000 : ℝ), (2632746381/5000000000 : ℝ)] ![(13203494623281/100000000000000 : ℝ), (688882751507/1562500000000 : ℝ), (21354004631579/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2173114883/10000000000 : ℝ)|^4161 ≤ (13203494623281/100000000000000 : ℝ)^3137
        have hw : |(-2173114883/10000000000 : ℝ)|=(2173114883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539330453/1000000000 : ℝ)|^4161 ≤ (688882751507/1562500000000 : ℝ)^3137
        have hw : |(539330453/1000000000 : ℝ)|=(539330453/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632746381/5000000000 : ℝ)|^4161 ≤ (21354004631579/50000000000000 : ℝ)^3137
        have hw : |(2632746381/5000000000 : ℝ)|=(2632746381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s7_1 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068962709/2000000000 : ℝ)*x 0 + (-2237947029/10000000000 : ℝ)*x 1 + (5265492767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068962709/2000000000 : ℝ)^4161 ≤ (5445434567507/12500000000000 : ℝ)^3137 := by
    have hnat : (1068962709 : ℕ)^4161*12500000000000^3137 ≤ 5445434567507^3137*2000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068962709 2000000000 5445434567507 12500000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2237947029/10000000000 : ℝ)^4161 ≤ (13728514129979/100000000000000 : ℝ)^3137 := by
    have hnat : (2237947029 : ℕ)^4161*100000000000000^3137 ≤ 13728514129979^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237947029 10000000000 13728514129979 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265492767/10000000000 : ℝ)^4161 ≤ (854160186339/2000000000000 : ℝ)^3137 := by
    have hnat : (5265492767 : ℕ)^4161*2000000000000^3137 ≤ 854160186339^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265492767 10000000000 854160186339 2000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068962709/2000000000 : ℝ), (-2237947029/10000000000 : ℝ), (5265492767/10000000000 : ℝ)] ![(5445434567507/12500000000000 : ℝ), (13728514129979/100000000000000 : ℝ), (854160186339/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068962709/2000000000 : ℝ)|^4161 ≤ (5445434567507/12500000000000 : ℝ)^3137
        have hw : |(1068962709/2000000000 : ℝ)|=(1068962709/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2237947029/10000000000 : ℝ)|^4161 ≤ (13728514129979/100000000000000 : ℝ)^3137
        have hw : |(-2237947029/10000000000 : ℝ)|=(2237947029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265492767/10000000000 : ℝ)|^4161 ≤ (854160186339/2000000000000 : ℝ)^3137
        have hw : |(5265492767/10000000000 : ℝ)|=(5265492767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s7_2 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344813547/10000000000 : ℝ)*x 0 + (5265492769/10000000000 : ℝ)*x 1 + (-139871689/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344813547/10000000000 : ℝ)^4161 ≤ (21781738280839/50000000000000 : ℝ)^3137 := by
    have hnat : (5344813547 : ℕ)^4161*50000000000000^3137 ≤ 21781738280839^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344813547 10000000000 21781738280839 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265492769/10000000000 : ℝ)^4161 ≤ (42708009338467/100000000000000 : ℝ)^3137 := by
    have hnat : (5265492769 : ℕ)^4161*100000000000000^3137 ≤ 42708009338467^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265492769 10000000000 42708009338467 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (139871689/625000000 : ℝ)^4161 ≤ (2745702817859/20000000000000 : ℝ)^3137 := by
    have hnat : (139871689 : ℕ)^4161*20000000000000^3137 ≤ 2745702817859^3137*625000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139871689 625000000 2745702817859 20000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344813547/10000000000 : ℝ), (5265492769/10000000000 : ℝ), (-139871689/625000000 : ℝ)] ![(21781738280839/50000000000000 : ℝ), (42708009338467/100000000000000 : ℝ), (2745702817859/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344813547/10000000000 : ℝ)|^4161 ≤ (21781738280839/50000000000000 : ℝ)^3137
        have hw : |(5344813547/10000000000 : ℝ)|=(5344813547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265492769/10000000000 : ℝ)|^4161 ≤ (42708009338467/100000000000000 : ℝ)^3137
        have hw : |(5265492769/10000000000 : ℝ)|=(5265492769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-139871689/625000000 : ℝ)|^4161 ≤ (2745702817859/20000000000000 : ℝ)^3137
        have hw : |(-139871689/625000000 : ℝ)|=(139871689/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s7_3 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4366505937/10000000000 : ℝ)*x 0 + (4241529047/10000000000 : ℝ)*x 1 + (899031801/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4366505937/10000000000 : ℝ)^4161 ≤ (33316875513673/100000000000000 : ℝ)^3137 := by
    have hnat : (4366505937 : ℕ)^4161*100000000000000^3137 ≤ 33316875513673^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366505937 10000000000 33316875513673 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4241529047/10000000000 : ℝ)^4161 ≤ (1602898037363/5000000000000 : ℝ)^3137 := by
    have hnat : (4241529047 : ℕ)^4161*5000000000000^3137 ≤ 1602898037363^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241529047 10000000000 1602898037363 5000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (899031801/2000000000 : ℝ)^4161 ≤ (34625163717267/100000000000000 : ℝ)^3137 := by
    have hnat : (899031801 : ℕ)^4161*100000000000000^3137 ≤ 34625163717267^3137*2000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899031801 2000000000 34625163717267 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4366505937/10000000000 : ℝ), (4241529047/10000000000 : ℝ), (899031801/2000000000 : ℝ)] ![(33316875513673/100000000000000 : ℝ), (1602898037363/5000000000000 : ℝ), (34625163717267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4366505937/10000000000 : ℝ)|^4161 ≤ (33316875513673/100000000000000 : ℝ)^3137
        have hw : |(4366505937/10000000000 : ℝ)|=(4366505937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4241529047/10000000000 : ℝ)|^4161 ≤ (1602898037363/5000000000000 : ℝ)^3137
        have hw : |(4241529047/10000000000 : ℝ)|=(4241529047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(899031801/2000000000 : ℝ)|^4161 ≤ (34625163717267/100000000000000 : ℝ)^3137
        have hw : |(899031801/2000000000 : ℝ)|=(899031801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s7_4 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-10865599/50000000 : ℝ)*x 0 + (5265813917/10000000000 : ℝ)*x 1 + (2696491109/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10865599/50000000 : ℝ)^4161 ≤ (13203534250151/100000000000000 : ℝ)^3137 := by
    have hnat : (10865599 : ℕ)^4161*100000000000000^3137 ≤ 13203534250151^3137*50000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10865599 50000000 13203534250151 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265813917/10000000000 : ℝ)^4161 ≤ (42711464457789/100000000000000 : ℝ)^3137 := by
    have hnat : (5265813917 : ℕ)^4161*100000000000000^3137 ≤ 42711464457789^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265813917 10000000000 42711464457789 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696491109/5000000000 : ℝ)^4161 ≤ (1102125031717/2500000000000 : ℝ)^3137 := by
    have hnat : (2696491109 : ℕ)^4161*2500000000000^3137 ≤ 1102125031717^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696491109 5000000000 1102125031717 2500000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-10865599/50000000 : ℝ), (5265813917/10000000000 : ℝ), (2696491109/5000000000 : ℝ)] ![(13203534250151/100000000000000 : ℝ), (42711464457789/100000000000000 : ℝ), (1102125031717/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-10865599/50000000 : ℝ)|^4161 ≤ (13203534250151/100000000000000 : ℝ)^3137
        have hw : |(-10865599/50000000 : ℝ)|=(10865599/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265813917/10000000000 : ℝ)|^4161 ≤ (42711464457789/100000000000000 : ℝ)^3137
        have hw : |(5265813917/10000000000 : ℝ)|=(5265813917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696491109/5000000000 : ℝ)|^4161 ≤ (1102125031717/2500000000000 : ℝ)^3137
        have hw : |(2696491109/5000000000 : ℝ)|=(2696491109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s7_5 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312463197/10000000000 : ℝ)*x 0 + (-263807197/1250000000 : ℝ)*x 1 + (2696491109/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312463197/10000000000 : ℝ)^4161 ≤ (10803519255857/25000000000000 : ℝ)^3137 := by
    have hnat : (5312463197 : ℕ)^4161*25000000000000^3137 ≤ 10803519255857^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312463197 10000000000 10803519255857 25000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263807197/1250000000 : ℝ)^4161 ≤ (3175230422967/25000000000000 : ℝ)^3137 := by
    have hnat : (263807197 : ℕ)^4161*25000000000000^3137 ≤ 3175230422967^3137*1250000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263807197 1250000000 3175230422967 25000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696491109/5000000000 : ℝ)^4161 ≤ (1102125031717/2500000000000 : ℝ)^3137 := by
    have hnat : (2696491109 : ℕ)^4161*2500000000000^3137 ≤ 1102125031717^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696491109 5000000000 1102125031717 2500000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312463197/10000000000 : ℝ), (-263807197/1250000000 : ℝ), (2696491109/5000000000 : ℝ)] ![(10803519255857/25000000000000 : ℝ), (3175230422967/25000000000000 : ℝ), (1102125031717/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312463197/10000000000 : ℝ)|^4161 ≤ (10803519255857/25000000000000 : ℝ)^3137
        have hw : |(5312463197/10000000000 : ℝ)|=(5312463197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-263807197/1250000000 : ℝ)|^4161 ≤ (3175230422967/25000000000000 : ℝ)^3137
        have hw : |(-263807197/1250000000 : ℝ)|=(263807197/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696491109/5000000000 : ℝ)|^4161 ≤ (1102125031717/2500000000000 : ℝ)^3137
        have hw : |(2696491109/5000000000 : ℝ)|=(2696491109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s7_6 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312463197/10000000000 : ℝ)*x 0 + (2696491109/5000000000 : ℝ)*x 1 + (-263807197/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312463197/10000000000 : ℝ)^4161 ≤ (10803519255857/25000000000000 : ℝ)^3137 := by
    have hnat : (5312463197 : ℕ)^4161*25000000000000^3137 ≤ 10803519255857^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312463197 10000000000 10803519255857 25000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696491109/5000000000 : ℝ)^4161 ≤ (1102125031717/2500000000000 : ℝ)^3137 := by
    have hnat : (2696491109 : ℕ)^4161*2500000000000^3137 ≤ 1102125031717^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696491109 5000000000 1102125031717 2500000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263807197/1250000000 : ℝ)^4161 ≤ (3175230422967/25000000000000 : ℝ)^3137 := by
    have hnat : (263807197 : ℕ)^4161*25000000000000^3137 ≤ 3175230422967^3137*1250000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263807197 1250000000 3175230422967 25000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312463197/10000000000 : ℝ), (2696491109/5000000000 : ℝ), (-263807197/1250000000 : ℝ)] ![(10803519255857/25000000000000 : ℝ), (1102125031717/2500000000000 : ℝ), (3175230422967/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312463197/10000000000 : ℝ)|^4161 ≤ (10803519255857/25000000000000 : ℝ)^3137
        have hw : |(5312463197/10000000000 : ℝ)|=(5312463197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696491109/5000000000 : ℝ)|^4161 ≤ (1102125031717/2500000000000 : ℝ)^3137
        have hw : |(2696491109/5000000000 : ℝ)|=(2696491109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-263807197/1250000000 : ℝ)|^4161 ≤ (3175230422967/25000000000000 : ℝ)^3137
        have hw : |(-263807197/1250000000 : ℝ)|=(263807197/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s7_7 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (873303141/2000000000 : ℝ)*x 0 + (2247260863/5000000000 : ℝ)*x 1 + (4242168631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873303141/2000000000 : ℝ)^4161 ≤ (33316974373357/100000000000000 : ℝ)^3137 := by
    have hnat : (873303141 : ℕ)^4161*100000000000000^3137 ≤ 33316974373357^3137*2000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873303141 2000000000 33316974373357 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2247260863/5000000000 : ℝ)^4161 ≤ (34618652689727/100000000000000 : ℝ)^3137 := by
    have hnat : (2247260863 : ℕ)^4161*100000000000000^3137 ≤ 34618652689727^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247260863 5000000000 34618652689727 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4242168631/10000000000 : ℝ)^4161 ≤ (16032186457857/50000000000000 : ℝ)^3137 := by
    have hnat : (4242168631 : ℕ)^4161*50000000000000^3137 ≤ 16032186457857^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242168631 10000000000 16032186457857 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873303141/2000000000 : ℝ), (2247260863/5000000000 : ℝ), (4242168631/10000000000 : ℝ)] ![(33316974373357/100000000000000 : ℝ), (34618652689727/100000000000000 : ℝ), (16032186457857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873303141/2000000000 : ℝ)|^4161 ≤ (33316974373357/100000000000000 : ℝ)^3137
        have hw : |(873303141/2000000000 : ℝ)|=(873303141/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2247260863/5000000000 : ℝ)|^4161 ≤ (34618652689727/100000000000000 : ℝ)^3137
        have hw : |(2247260863/5000000000 : ℝ)|=(2247260863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4242168631/10000000000 : ℝ)|^4161 ≤ (16032186457857/50000000000000 : ℝ)^3137
        have hw : |(4242168631/10000000000 : ℝ)|=(4242168631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1129_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193761/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (281/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (354/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (2267/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14043/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (281/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (354/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (281/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (354/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (281/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (354/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (281/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (354/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (281/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (354/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (281/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (354/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (354/3125 : ℝ) ^ (8321/2048 : ℝ) ≤ (14356074376161227/100000000000000000000 : ℝ) := by
    have hpowers : (354/3125 : ℝ)^8321 ≤ (14356074376161227/100000000000000000000 : ℝ)^2048 := by
      have hnat : (354 : ℕ)^8321*100000000000000000000^2048 ≤ 14356074376161227^2048*3125^8321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        354 3125 14356074376161227 100000000000000000000 8321 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (354/3125 : ℝ)) (X := (14356074376161227/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (281/2000 : ℝ) ^ (8321/2048 : ℝ) ≤ (688729823397031/2000000000000000000 : ℝ) := by
    have hpowers : (281/2000 : ℝ)^8321 ≤ (688729823397031/2000000000000000000 : ℝ)^2048 := by
      have hnat : (281 : ℕ)^8321*2000000000000000000^2048 ≤ 688729823397031^2048*2000^8321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        281 2000 688729823397031 2000000000000000000 8321 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (281/2000 : ℝ)) (X := (688729823397031/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014356074376161227/50000000000000000000 : ℝ) ≤ (5000353299589587/5000000000000000 : ℝ) ^ (8321/2048 : ℝ) := by
    have hpowers : (50014356074376161227/50000000000000000000 : ℝ)^2048 ≤ (5000353299589587/5000000000000000 : ℝ)^8321 := by
      have hnat : (50014356074376161227 : ℕ)^2048*5000000000000000^8321 ≤ 5000353299589587^8321*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014356074376161227 50000000000000000000 5000353299589587 5000000000000000 2048 8321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000353299589587/5000000000000000 : ℝ)) (X := (50014356074376161227/50000000000000000000 : ℝ)) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048792565546012777/100000000000000000000 : ℝ) ≤ (10001200682623571/10000000000000000 : ℝ) ^ (8321/2048 : ℝ) := by
    have hpowers : (100048792565546012777/100000000000000000000 : ℝ)^2048 ≤ (10001200682623571/10000000000000000 : ℝ)^8321 := by
      have hnat : (100048792565546012777 : ℕ)^2048*10000000000000000^8321 ≤ 10001200682623571^8321*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048792565546012777 100000000000000000000 10001200682623571 10000000000000000 2048 8321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001200682623571/10000000000000000 : ℝ)) (X := (100048792565546012777/100000000000000000000 : ℝ)) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (1000688729823397031/1000000000000000000 : ℝ) ≤ (39069120179953/39062500000000 : ℝ) ^ (8321/2048 : ℝ) := by
    have hpowers : (1000688729823397031/1000000000000000000 : ℝ)^2048 ≤ (39069120179953/39062500000000 : ℝ)^8321 := by
      have hnat : (1000688729823397031 : ℕ)^2048*39062500000000^8321 ≤ 39069120179953^8321*1000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000688729823397031 1000000000000000000 39069120179953 39062500000000 2048 8321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (39069120179953/39062500000000 : ℝ)) (X := (1000688729823397031/1000000000000000000 : ℝ)) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14356074376161227/100000000000000000000 : ℝ) ≤ ((6802682352112363299/6805000000000000000 : ℝ)+2*(494083444397/272200000000000 : ℝ)*(354/3125 : ℝ))^(8321/2048 : ℝ) := by
    rw [show (6802682352112363299/6805000000000000000 : ℝ)+2*(494083444397/272200000000000 : ℝ)*(354/3125 : ℝ)=(5000353299589587/5000000000000000 : ℝ) by norm_num, show 1+2*(14356074376161227/100000000000000000000 : ℝ)=(50014356074376161227/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(688729823397031/2000000000000000000 : ℝ)+(14356074376161227/100000000000000000000 : ℝ) ≤ ((6802682352112363299/6805000000000000000 : ℝ)+(494083444397/272200000000000 : ℝ)*((281/2000 : ℝ)+(354/3125 : ℝ)))^(8321/2048 : ℝ) := by
    rw [show (6802682352112363299/6805000000000000000 : ℝ)+(494083444397/272200000000000 : ℝ)*((281/2000 : ℝ)+(354/3125 : ℝ))=(10001200682623571/10000000000000000 : ℝ) by norm_num, show 1+(688729823397031/2000000000000000000 : ℝ)+(14356074376161227/100000000000000000000 : ℝ)=(100048792565546012777/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(688729823397031/2000000000000000000 : ℝ) ≤ ((6802682352112363299/6805000000000000000 : ℝ)+2*(494083444397/272200000000000 : ℝ)*(281/2000 : ℝ))^(8321/2048 : ℝ) := by
    rw [show (6802682352112363299/6805000000000000000 : ℝ)+2*(494083444397/272200000000000 : ℝ)*(281/2000 : ℝ)=(39069120179953/39062500000000 : ℝ) by norm_num, show 1+2*(688729823397031/2000000000000000000 : ℝ)=(1000688729823397031/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6802682352112363299/6805000000000000000 : ℝ)*(X 1 0+X 2 0)+(494083444397/272200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8321/2048 : ℝ)) (lo := (354/3125 : ℝ)) (hi := (281/2000 : ℝ)) (c := (6802682352112363299/6805000000000000000 : ℝ)) (alpha := (494083444397/272200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6802682352112363299/6805000000000000000 : ℝ)*(X 0 1+X 2 1)+(494083444397/272200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8321/2048 : ℝ)) (lo := (354/3125 : ℝ)) (hi := (281/2000 : ℝ)) (c := (6802682352112363299/6805000000000000000 : ℝ)) (alpha := (494083444397/272200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6802682352112363299/6805000000000000000 : ℝ)*(X 0 2+X 1 2)+(494083444397/272200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8321/2048 : ℝ)) (lo := (354/3125 : ℝ)) (hi := (281/2000 : ℝ)) (c := (6802682352112363299/6805000000000000000 : ℝ)) (alpha := (494083444397/272200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2173114883/10000000000 : ℝ)*X 0 0+(539330453/1000000000 : ℝ)*X 0 1+(2632746381/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068962709/2000000000 : ℝ)*X 1 0+(-2237947029/10000000000 : ℝ)*X 1 1+(5265492767/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344813547/10000000000 : ℝ)*X 2 0+(5265492769/10000000000 : ℝ)*X 2 1+(-139871689/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4366505937/10000000000 : ℝ)*X 0 0+(4241529047/10000000000 : ℝ)*X 0 1+(899031801/2000000000 : ℝ)*X 0 2+(4366505937/10000000000 : ℝ)*X 1 0+(4241529047/10000000000 : ℝ)*X 1 1+(899031801/2000000000 : ℝ)*X 1 2+(4366505937/10000000000 : ℝ)*X 2 0+(4241529047/10000000000 : ℝ)*X 2 1+(899031801/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-10865599/50000000 : ℝ)*X 0 0+(5265813917/10000000000 : ℝ)*X 0 1+(2696491109/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312463197/10000000000 : ℝ)*X 1 0+(-263807197/1250000000 : ℝ)*X 1 1+(2696491109/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312463197/10000000000 : ℝ)*X 2 0+(2696491109/5000000000 : ℝ)*X 2 1+(-263807197/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((873303141/2000000000 : ℝ)*X 0 0+(2247260863/5000000000 : ℝ)*X 0 1+(4242168631/10000000000 : ℝ)*X 0 2+(873303141/2000000000 : ℝ)*X 1 0+(2247260863/5000000000 : ℝ)*X 1 1+(4242168631/10000000000 : ℝ)*X 1 2+(873303141/2000000000 : ℝ)*X 2 0+(2247260863/5000000000 : ℝ)*X 2 1+(4242168631/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (114735843591254598353931/13610000000000000000000000000 : ℝ) := by norm_num
    linear_combination (41964433/2500000000000 : ℝ)*(base19) + (196764953/12500000000000 : ℝ)*(base23) + (57395513/100000000000000 : ℝ)*(lower2) + (208634747/100000000000000 : ℝ)*(upper3) + (27566619/20000000000000 : ℝ)*(upper5) + (5883449516712669/100000000000000 : ℝ)*(major0) + (5883449516712669/100000000000000 : ℝ)*(major1) + (5883449516712669/100000000000000 : ℝ)*(major2) + (782405352733991/10000000000000 : ℝ)*(sp0) + (7824098127174011/100000000000000 : ℝ)*(sp1) + (7824098231631707/100000000000000 : ℝ)*(sp2) + (3942774351747917/100000000000000 : ℝ)*(sp3) + (46278411421/100000000000000 : ℝ)*(sp4) + (122974587/500000000000 : ℝ)*(sp7) + (1971399473332659/50000000000000 : ℝ)*(f.failure) + (7824099805751331/100000000000000 : ℝ)*(f.sum) + (38355590600203/13610000000000000000000000000 : ℝ)*base65 + (5027590536744239969/680500000000000000000000000000000 : ℝ)*base68 + (7668464396232260031/680500000000000000000000000000000 : ℝ)*base69 + (740449633668239969/680500000000000000000000000000000 : ℝ)*base72 + (66790918024207/13610000000000000000000000000 : ℝ)*base74 + (10995404916092760031/680500000000000000000000000000000 : ℝ)*base75 + (16324070689344760031/680500000000000000000000000000000 : ℝ)*base77 + (3308163242587239969/680500000000000000000000000000000 : ℝ)*base80 + (1330972214223/13610000000000000000000000000 : ℝ)*base81 + (740499/40000000000000000000 : ℝ)*base89 + (740499/40000000000000000000 : ℝ)*base91 + (740499/40000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (45695694403598227426631217/4253125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (98575741/5000000000000 : ℝ)*(base19) + (2143829161/100000000000000 : ℝ)*(base23) + (215806909/100000000000000 : ℝ)*(upper3) + (244917/312500000000 : ℝ)*(lower4) + (219398331/100000000000000 : ℝ)*(upper5) + (18478584598797/312500000000 : ℝ)*(major0) + (18478584598797/312500000000 : ℝ)*(major1) + (18478584598797/312500000000 : ℝ)*(major2) + (54316138971/100000000000000 : ℝ)*(sp1) + (14596636631/25000000000000 : ℝ)*(sp2) + (7863592995497183/100000000000000 : ℝ)*(sp4) + (122867761060053/1562500000000 : ℝ)*(sp5) + (7863532465121497/100000000000000 : ℝ)*(sp6) + (1981350394799307/50000000000000 : ℝ)*(sp7) + (1981350394799307/50000000000000 : ℝ)*(f.failure) + (7863592995497183/100000000000000 : ℝ)*(f.sum) + (1415031152209/680500000000000000000000000 : ℝ)*base65 + (4205201472730731/4253125000000000000000000000000 : ℝ)*base67 + (27017862596001303/2126562500000000000000000000000 : ℝ)*base69 + (83539355764124481/4253125000000000000000000000000 : ℝ)*base71 + (473321543081/272200000000000000000000000 : ℝ)*base74 + (31221816729005731/4253125000000000000000000000000 : ℝ)*base75 + (9432054637255731/4253125000000000000000000000000 : ℝ)*base77 + (19170751120330339/1063281250000000000000000000000 : ℝ)*base79 + (2906202557271/680500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (476373/40000000000000000000 : ℝ)*base90 + (476373/40000000000000000000 : ℝ)*base92 + (476373/40000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1129_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193761/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (281/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (354/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2267/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14043/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1129_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1129_s8_0 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2173120007/10000000000 : ℝ)*x 0 + (5393233671/10000000000 : ℝ)*x 1 + (5265560339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173120007/10000000000 : ℝ)^4161 ≤ (13203535918397/100000000000000 : ℝ)^3137 := by
    have hnat : (2173120007 : ℕ)^4161*100000000000000^3137 ≤ 13203535918397^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173120007 10000000000 13203535918397 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393233671/10000000000 : ℝ)^4161 ≤ (44087727766739/100000000000000 : ℝ)^3137 := by
    have hnat : (5393233671 : ℕ)^4161*100000000000000^3137 ≤ 44087727766739^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393233671 10000000000 44087727766739 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265560339/10000000000 : ℝ)^4161 ≤ (42708736294817/100000000000000 : ℝ)^3137 := by
    have hnat : (5265560339 : ℕ)^4161*100000000000000^3137 ≤ 42708736294817^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265560339 10000000000 42708736294817 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2173120007/10000000000 : ℝ), (5393233671/10000000000 : ℝ), (5265560339/10000000000 : ℝ)] ![(13203535918397/100000000000000 : ℝ), (44087727766739/100000000000000 : ℝ), (42708736294817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2173120007/10000000000 : ℝ)|^4161 ≤ (13203535918397/100000000000000 : ℝ)^3137
        have hw : |(-2173120007/10000000000 : ℝ)|=(2173120007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393233671/10000000000 : ℝ)|^4161 ≤ (44087727766739/100000000000000 : ℝ)^3137
        have hw : |(5393233671/10000000000 : ℝ)|=(5393233671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265560339/10000000000 : ℝ)|^4161 ≤ (42708736294817/100000000000000 : ℝ)^3137
        have hw : |(5265560339/10000000000 : ℝ)|=(5265560339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s8_1 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344796043/10000000000 : ℝ)*x 0 + (-111894047/500000000 : ℝ)*x 1 + (2632780169/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344796043/10000000000 : ℝ)^4161 ≤ (21781643661427/50000000000000 : ℝ)^3137 := by
    have hnat : (5344796043 : ℕ)^4161*50000000000000^3137 ≤ 21781643661427^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344796043 10000000000 21781643661427 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (111894047/500000000 : ℝ)^4161 ≤ (549119055021/4000000000000 : ℝ)^3137 := by
    have hnat : (111894047 : ℕ)^4161*4000000000000^3137 ≤ 549119055021^3137*500000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111894047 500000000 549119055021 4000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632780169/5000000000 : ℝ)^4161 ≤ (21354368142029/50000000000000 : ℝ)^3137 := by
    have hnat : (2632780169 : ℕ)^4161*50000000000000^3137 ≤ 21354368142029^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632780169 5000000000 21354368142029 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344796043/10000000000 : ℝ), (-111894047/500000000 : ℝ), (2632780169/5000000000 : ℝ)] ![(21781643661427/50000000000000 : ℝ), (549119055021/4000000000000 : ℝ), (21354368142029/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344796043/10000000000 : ℝ)|^4161 ≤ (21781643661427/50000000000000 : ℝ)^3137
        have hw : |(5344796043/10000000000 : ℝ)|=(5344796043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-111894047/500000000 : ℝ)|^4161 ≤ (549119055021/4000000000000 : ℝ)^3137
        have hw : |(-111894047/500000000 : ℝ)|=(111894047/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632780169/5000000000 : ℝ)|^4161 ≤ (21354368142029/50000000000000 : ℝ)^3137
        have hw : |(2632780169/5000000000 : ℝ)|=(2632780169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s8_2 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336199011/2500000000 : ℝ)*x 0 + (2632780169/5000000000 : ℝ)*x 1 + (-2237880939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336199011/2500000000 : ℝ)^4161 ≤ (8712657466733/20000000000000 : ℝ)^3137 := by
    have hnat : (1336199011 : ℕ)^4161*20000000000000^3137 ≤ 8712657466733^3137*2500000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336199011 2500000000 8712657466733 20000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632780169/5000000000 : ℝ)^4161 ≤ (21354368142029/50000000000000 : ℝ)^3137 := by
    have hnat : (2632780169 : ℕ)^4161*50000000000000^3137 ≤ 21354368142029^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632780169 5000000000 21354368142029 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2237880939/10000000000 : ℝ)^4161 ≤ (3431994091847/25000000000000 : ℝ)^3137 := by
    have hnat : (2237880939 : ℕ)^4161*25000000000000^3137 ≤ 3431994091847^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237880939 10000000000 3431994091847 25000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336199011/2500000000 : ℝ), (2632780169/5000000000 : ℝ), (-2237880939/10000000000 : ℝ)] ![(8712657466733/20000000000000 : ℝ), (21354368142029/50000000000000 : ℝ), (3431994091847/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336199011/2500000000 : ℝ)|^4161 ≤ (8712657466733/20000000000000 : ℝ)^3137
        have hw : |(1336199011/2500000000 : ℝ)|=(1336199011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632780169/5000000000 : ℝ)|^4161 ≤ (21354368142029/50000000000000 : ℝ)^3137
        have hw : |(2632780169/5000000000 : ℝ)|=(2632780169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2237880939/10000000000 : ℝ)|^4161 ≤ (3431994091847/25000000000000 : ℝ)^3137
        have hw : |(-2237880939/10000000000 : ℝ)|=(2237880939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s8_3 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4366509453/10000000000 : ℝ)*x 0 + (4241665931/10000000000 : ℝ)*x 1 + (561877651/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4366509453/10000000000 : ℝ)^4161 ≤ (8329227774573/25000000000000 : ℝ)^3137 := by
    have hnat : (4366509453 : ℕ)^4161*25000000000000^3137 ≤ 8329227774573^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366509453 10000000000 8329227774573 25000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4241665931/10000000000 : ℝ)^4161 ≤ (32059333055337/100000000000000 : ℝ)^3137 := by
    have hnat : (4241665931 : ℕ)^4161*100000000000000^3137 ≤ 32059333055337^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241665931 10000000000 32059333055337 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (561877651/1250000000 : ℝ)^4161 ≤ (34623755831029/100000000000000 : ℝ)^3137 := by
    have hnat : (561877651 : ℕ)^4161*100000000000000^3137 ≤ 34623755831029^3137*1250000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561877651 1250000000 34623755831029 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4366509453/10000000000 : ℝ), (4241665931/10000000000 : ℝ), (561877651/1250000000 : ℝ)] ![(8329227774573/25000000000000 : ℝ), (32059333055337/100000000000000 : ℝ), (34623755831029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4366509453/10000000000 : ℝ)|^4161 ≤ (8329227774573/25000000000000 : ℝ)^3137
        have hw : |(4366509453/10000000000 : ℝ)|=(4366509453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4241665931/10000000000 : ℝ)|^4161 ≤ (32059333055337/100000000000000 : ℝ)^3137
        have hw : |(4241665931/10000000000 : ℝ)|=(4241665931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(561877651/1250000000 : ℝ)|^4161 ≤ (34623755831029/100000000000000 : ℝ)^3137
        have hw : |(561877651/1250000000 : ℝ)|=(561877651/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s8_4 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2173125111/10000000000 : ℝ)*x 0 + (5265880729/10000000000 : ℝ)*x 1 + (2696455989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173125111/10000000000 : ℝ)^4161 ≤ (6601788526181/50000000000000 : ℝ)^3137 := by
    have hnat : (2173125111 : ℕ)^4161*50000000000000^3137 ≤ 6601788526181^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173125111 10000000000 6601788526181 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265880729/10000000000 : ℝ)^4161 ≤ (21356091636719/50000000000000 : ℝ)^3137 := by
    have hnat : (5265880729 : ℕ)^4161*50000000000000^3137 ≤ 21356091636719^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265880729 10000000000 21356091636719 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696455989/5000000000 : ℝ)^4161 ≤ (551052995821/1250000000000 : ℝ)^3137 := by
    have hnat : (2696455989 : ℕ)^4161*1250000000000^3137 ≤ 551052995821^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696455989 5000000000 551052995821 1250000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2173125111/10000000000 : ℝ), (5265880729/10000000000 : ℝ), (2696455989/5000000000 : ℝ)] ![(6601788526181/50000000000000 : ℝ), (21356091636719/50000000000000 : ℝ), (551052995821/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2173125111/10000000000 : ℝ)|^4161 ≤ (6601788526181/50000000000000 : ℝ)^3137
        have hw : |(-2173125111/10000000000 : ℝ)|=(2173125111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265880729/10000000000 : ℝ)|^4161 ≤ (21356091636719/50000000000000 : ℝ)^3137
        have hw : |(5265880729/10000000000 : ℝ)|=(5265880729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696455989/5000000000 : ℝ)|^4161 ≤ (551052995821/1250000000000 : ℝ)^3137
        have hw : |(2696455989/5000000000 : ℝ)|=(2696455989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s8_5 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656240349/5000000000 : ℝ)*x 0 + (-211052933/1000000000 : ℝ)*x 1 + (5392911977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656240349/5000000000 : ℝ)^4161 ≤ (43214265855433/100000000000000 : ℝ)^3137 := by
    have hnat : (2656240349 : ℕ)^4161*100000000000000^3137 ≤ 43214265855433^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656240349 5000000000 43214265855433 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211052933/1000000000 : ℝ)^4161 ≤ (793843404697/6250000000000 : ℝ)^3137 := by
    have hnat : (211052933 : ℕ)^4161*6250000000000^3137 ≤ 793843404697^3137*1000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211052933 1000000000 793843404697 6250000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392911977/10000000000 : ℝ)^4161 ≤ (44084239654837/100000000000000 : ℝ)^3137 := by
    have hnat : (5392911977 : ℕ)^4161*100000000000000^3137 ≤ 44084239654837^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392911977 10000000000 44084239654837 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656240349/5000000000 : ℝ), (-211052933/1000000000 : ℝ), (5392911977/10000000000 : ℝ)] ![(43214265855433/100000000000000 : ℝ), (793843404697/6250000000000 : ℝ), (44084239654837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656240349/5000000000 : ℝ)|^4161 ≤ (43214265855433/100000000000000 : ℝ)^3137
        have hw : |(2656240349/5000000000 : ℝ)|=(2656240349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-211052933/1000000000 : ℝ)|^4161 ≤ (793843404697/6250000000000 : ℝ)^3137
        have hw : |(-211052933/1000000000 : ℝ)|=(211052933/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392911977/10000000000 : ℝ)|^4161 ≤ (44084239654837/100000000000000 : ℝ)^3137
        have hw : |(5392911977/10000000000 : ℝ)|=(5392911977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s8_6 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062496133/2000000000 : ℝ)*x 0 + (1348228027/2500000000 : ℝ)*x 1 + (-2110529197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062496133/2000000000 : ℝ)^4161 ≤ (4321426549937/10000000000000 : ℝ)^3137 := by
    have hnat : (1062496133 : ℕ)^4161*10000000000000^3137 ≤ 4321426549937^3137*2000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062496133 2000000000 4321426549937 10000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348228027/2500000000 : ℝ)^4161 ≤ (176336964301/400000000000 : ℝ)^3137 := by
    have hnat : (1348228027 : ℕ)^4161*400000000000^3137 ≤ 176336964301^3137*2500000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348228027 2500000000 176336964301 400000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2110529197/10000000000 : ℝ)^4161 ≤ (635074670673/5000000000000 : ℝ)^3137 := by
    have hnat : (2110529197 : ℕ)^4161*5000000000000^3137 ≤ 635074670673^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110529197 10000000000 635074670673 5000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062496133/2000000000 : ℝ), (1348228027/2500000000 : ℝ), (-2110529197/10000000000 : ℝ)] ![(4321426549937/10000000000000 : ℝ), (176336964301/400000000000 : ℝ), (635074670673/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062496133/2000000000 : ℝ)|^4161 ≤ (4321426549937/10000000000000 : ℝ)^3137
        have hw : |(1062496133/2000000000 : ℝ)|=(1062496133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348228027/2500000000 : ℝ)|^4161 ≤ (176336964301/400000000000 : ℝ)^3137
        have hw : |(1348228027/2500000000 : ℝ)|=(1348228027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2110529197/10000000000 : ℝ)|^4161 ≤ (635074670673/5000000000000 : ℝ)^3137
        have hw : |(-2110529197/10000000000 : ℝ)|=(2110529197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s8_7 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1091629843/2500000000 : ℝ)*x 0 + (4494385239/10000000000 : ℝ)*x 1 + (2121152007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091629843/2500000000 : ℝ)^4161 ≤ (208231321789/625000000000 : ℝ)^3137 := by
    have hnat : (1091629843 : ℕ)^4161*625000000000^3137 ≤ 208231321789^3137*2500000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091629843 2500000000 208231321789 625000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4494385239/10000000000 : ℝ)^4161 ≤ (17308629126183/50000000000000 : ℝ)^3137 := by
    have hnat : (4494385239 : ℕ)^4161*50000000000000^3137 ≤ 17308629126183^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494385239 10000000000 17308629126183 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2121152007/5000000000 : ℝ)^4161 ≤ (16032865121243/50000000000000 : ℝ)^3137 := by
    have hnat : (2121152007 : ℕ)^4161*50000000000000^3137 ≤ 16032865121243^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121152007 5000000000 16032865121243 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1091629843/2500000000 : ℝ), (4494385239/10000000000 : ℝ), (2121152007/5000000000 : ℝ)] ![(208231321789/625000000000 : ℝ), (17308629126183/50000000000000 : ℝ), (16032865121243/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1091629843/2500000000 : ℝ)|^4161 ≤ (208231321789/625000000000 : ℝ)^3137
        have hw : |(1091629843/2500000000 : ℝ)|=(1091629843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4494385239/10000000000 : ℝ)|^4161 ≤ (17308629126183/50000000000000 : ℝ)^3137
        have hw : |(4494385239/10000000000 : ℝ)|=(4494385239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2121152007/5000000000 : ℝ)|^4161 ≤ (16032865121243/50000000000000 : ℝ)^3137
        have hw : |(2121152007/5000000000 : ℝ)|=(2121152007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1129_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193761/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14043/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2267/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11337/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14041/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14043/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2267/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14043/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2267/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14043/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2267/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14043/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2267/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14043/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2267/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14043/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2267/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2267/20000 : ℝ) ^ (8321/2048 : ℝ) ≤ (14392151927360151/100000000000000000000 : ℝ) := by
    have hpowers : (2267/20000 : ℝ)^8321 ≤ (14392151927360151/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2267 : ℕ)^8321*100000000000000000000^2048 ≤ 14392151927360151^2048*20000^8321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2267 20000 14392151927360151 100000000000000000000 8321 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2267/20000 : ℝ)) (X := (14392151927360151/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14043/100000 : ℝ) ^ (8321/2048 : ℝ) ≤ (34366835769949897/100000000000000000000 : ℝ) := by
    have hpowers : (14043/100000 : ℝ)^8321 ≤ (34366835769949897/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14043 : ℕ)^8321*100000000000000000000^2048 ≤ 34366835769949897^2048*100000^8321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14043 100000 34366835769949897 100000000000000000000 8321 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14043/100000 : ℝ)) (X := (34366835769949897/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014392151927360151/50000000000000000000 : ℝ) ≤ (10000708374706531/10000000000000000 : ℝ) ^ (8321/2048 : ℝ) := by
    have hpowers : (50014392151927360151/50000000000000000000 : ℝ)^2048 ≤ (10000708374706531/10000000000000000 : ℝ)^8321 := by
      have hnat : (50014392151927360151 : ℕ)^2048*10000000000000000^8321 ≤ 10000708374706531^8321*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014392151927360151 50000000000000000000 10000708374706531 10000000000000000 2048 8321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000708374706531/10000000000000000 : ℝ)) (X := (50014392151927360151/50000000000000000000 : ℝ)) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126523718365540939/3125000000000000000 : ℝ) ≤ (5000599928247499/5000000000000000 : ℝ) ^ (8321/2048 : ℝ) := by
    have hpowers : (3126523718365540939/3125000000000000000 : ℝ)^2048 ≤ (5000599928247499/5000000000000000 : ℝ)^8321 := by
      have hnat : (3126523718365540939 : ℕ)^2048*5000000000000000^8321 ≤ 5000599928247499^8321*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126523718365540939 3125000000000000000 5000599928247499 5000000000000000 2048 8321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000599928247499/5000000000000000 : ℝ)) (X := (3126523718365540939/3125000000000000000 : ℝ)) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034366835769949897/50000000000000000000 : ℝ) ≤ (2000338267656693/2000000000000000 : ℝ) ^ (8321/2048 : ℝ) := by
    have hpowers : (50034366835769949897/50000000000000000000 : ℝ)^2048 ≤ (2000338267656693/2000000000000000 : ℝ)^8321 := by
      have hnat : (50034366835769949897 : ℕ)^2048*2000000000000000^8321 ≤ 2000338267656693^8321*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034366835769949897 50000000000000000000 2000338267656693 2000000000000000 2048 8321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000338267656693/2000000000000000 : ℝ)) (X := (50034366835769949897/50000000000000000000 : ℝ)) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14392151927360151/100000000000000000000 : ℝ) ≤ ((13535388193280369529/13540000000000000000 : ℝ)+2*(491481788467/270800000000000 : ℝ)*(2267/20000 : ℝ))^(8321/2048 : ℝ) := by
    rw [show (13535388193280369529/13540000000000000000 : ℝ)+2*(491481788467/270800000000000 : ℝ)*(2267/20000 : ℝ)=(10000708374706531/10000000000000000 : ℝ) by norm_num, show 1+2*(14392151927360151/100000000000000000000 : ℝ)=(50014392151927360151/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34366835769949897/100000000000000000000 : ℝ)+(14392151927360151/100000000000000000000 : ℝ) ≤ ((13535388193280369529/13540000000000000000 : ℝ)+(491481788467/270800000000000 : ℝ)*((14043/100000 : ℝ)+(2267/20000 : ℝ)))^(8321/2048 : ℝ) := by
    rw [show (13535388193280369529/13540000000000000000 : ℝ)+(491481788467/270800000000000 : ℝ)*((14043/100000 : ℝ)+(2267/20000 : ℝ))=(5000599928247499/5000000000000000 : ℝ) by norm_num, show 1+(34366835769949897/100000000000000000000 : ℝ)+(14392151927360151/100000000000000000000 : ℝ)=(3126523718365540939/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34366835769949897/100000000000000000000 : ℝ) ≤ ((13535388193280369529/13540000000000000000 : ℝ)+2*(491481788467/270800000000000 : ℝ)*(14043/100000 : ℝ))^(8321/2048 : ℝ) := by
    rw [show (13535388193280369529/13540000000000000000 : ℝ)+2*(491481788467/270800000000000 : ℝ)*(14043/100000 : ℝ)=(2000338267656693/2000000000000000 : ℝ) by norm_num, show 1+2*(34366835769949897/100000000000000000000 : ℝ)=(50034366835769949897/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13535388193280369529/13540000000000000000 : ℝ)*(X 1 0+X 2 0)+(491481788467/270800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8321/2048 : ℝ)) (lo := (2267/20000 : ℝ)) (hi := (14043/100000 : ℝ)) (c := (13535388193280369529/13540000000000000000 : ℝ)) (alpha := (491481788467/270800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13535388193280369529/13540000000000000000 : ℝ)*(X 0 1+X 2 1)+(491481788467/270800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8321/2048 : ℝ)) (lo := (2267/20000 : ℝ)) (hi := (14043/100000 : ℝ)) (c := (13535388193280369529/13540000000000000000 : ℝ)) (alpha := (491481788467/270800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13535388193280369529/13540000000000000000 : ℝ)*(X 0 2+X 1 2)+(491481788467/270800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8321/2048 : ℝ)) (lo := (2267/20000 : ℝ)) (hi := (14043/100000 : ℝ)) (c := (13535388193280369529/13540000000000000000 : ℝ)) (alpha := (491481788467/270800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2173120007/10000000000 : ℝ)*X 0 0+(5393233671/10000000000 : ℝ)*X 0 1+(5265560339/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344796043/10000000000 : ℝ)*X 1 0+(-111894047/500000000 : ℝ)*X 1 1+(2632780169/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336199011/2500000000 : ℝ)*X 2 0+(2632780169/5000000000 : ℝ)*X 2 1+(-2237880939/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4366509453/10000000000 : ℝ)*X 0 0+(4241665931/10000000000 : ℝ)*X 0 1+(561877651/1250000000 : ℝ)*X 0 2+(4366509453/10000000000 : ℝ)*X 1 0+(4241665931/10000000000 : ℝ)*X 1 1+(561877651/1250000000 : ℝ)*X 1 2+(4366509453/10000000000 : ℝ)*X 2 0+(4241665931/10000000000 : ℝ)*X 2 1+(561877651/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2173125111/10000000000 : ℝ)*X 0 0+(5265880729/10000000000 : ℝ)*X 0 1+(2696455989/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656240349/5000000000 : ℝ)*X 1 0+(-211052933/1000000000 : ℝ)*X 1 1+(5392911977/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062496133/2000000000 : ℝ)*X 2 0+(1348228027/2500000000 : ℝ)*X 2 1+(-2110529197/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1091629843/2500000000 : ℝ)*X 0 0+(4494385239/10000000000 : ℝ)*X 0 1+(2121152007/5000000000 : ℝ)*X 0 2+(1091629843/2500000000 : ℝ)*X 1 0+(4494385239/10000000000 : ℝ)*X 1 1+(2121152007/5000000000 : ℝ)*X 1 2+(1091629843/2500000000 : ℝ)*X 2 0+(4494385239/10000000000 : ℝ)*X 2 1+(2121152007/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (546221996297518239293898423/169250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (642508337/100000000000000 : ℝ)*(base19) + (29997491/5000000000000 : ℝ)*(base23) + (2941239/12500000000000 : ℝ)*(lower2) + (80688909/100000000000000 : ℝ)*(upper3) + (3136377/6250000000000 : ℝ)*(upper5) + (1472446199486229/25000000000000 : ℝ)*(major0) + (1472446199486229/25000000000000 : ℝ)*(major1) + (1472446199486229/25000000000000 : ℝ)*(major2) + (1566501491744911/20000000000000 : ℝ)*(sp0) + (7832524304764969/100000000000000 : ℝ)*(sp1) + (3916262173661743/50000000000000 : ℝ)*(sp2) + (789407016501719/20000000000000 : ℝ)*(sp3) + (17488548751/100000000000000 : ℝ)*(sp4) + (9458530971/100000000000000 : ℝ)*(sp7) + (1973522270519783/50000000000000 : ℝ)*(f.failure) + (3916262473636653/50000000000000 : ℝ)*(f.sum) + (5268357862529/1692500000000000000000000000 : ℝ)*base65 + (403319339140866141/338500000000000000000000000000000 : ℝ)*base67 + (1566730039100633859/338500000000000000000000000000000 : ℝ)*base70 + (830957109025133859/338500000000000000000000000000000 : ℝ)*base72 + (20109960644653/3385000000000000000000000000 : ℝ)*base73 + (1229301659087866141/338500000000000000000000000000000 : ℝ)*base75 + (20206185229633859/338500000000000000000000000000000 : ℝ)*base78 + (1468276740343133859/338500000000000000000000000000000 : ℝ)*base80 + (11672968274057/3385000000000000000000000000 : ℝ)*base82 + (273863/40000000000000000000 : ℝ)*base89 + (273863/40000000000000000000 : ℝ)*base91 + (273863/40000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (206628899466702496203/42312500000000000000000000 : ℝ) := by norm_num
    linear_combination (334491839/25000000000000 : ℝ)*(base19) + (1450778429/100000000000000 : ℝ)*(base23) + (386853831/100000000000000 : ℝ)*(lower1) + (23768863/50000000000000 : ℝ)*(upper2) + (28596537/12500000000000 : ℝ)*(upper3) + (199104171/100000000000000 : ℝ)*(upper5) + (295975152696183/5000000000000 : ℝ)*(major0) + (295975152696183/5000000000000 : ℝ)*(major1) + (295975152696183/5000000000000 : ℝ)*(major2) + (1484226891/12500000000000 : ℝ)*(sp2) + (1574409137649919/20000000000000 : ℝ)*(sp4) + (7872044350282239/100000000000000 : ℝ)*(sp5) + (7872032363656039/100000000000000 : ℝ)*(sp6) + (1983480128408839/50000000000000 : ℝ)*(sp7) + (1983480128408839/50000000000000 : ℝ)*(f.failure) + (1574409137649919/20000000000000 : ℝ)*(f.sum) + (629403049847/338500000000000000000000000 : ℝ)*base65 + (210924576276042193/67700000000000000000000000000000 : ℝ)*base68 + (5045032718165457807/67700000000000000000000000000000 : ℝ)*base69 + (59403259291742193/67700000000000000000000000000000 : ℝ)*base72 + (2341392060017/677000000000000000000000000 : ℝ)*base73 + (623929740119357807/67700000000000000000000000000000 : ℝ)*base75 + (368459607071757807/67700000000000000000000000000000 : ℝ)*base77 + (654972851687742193/67700000000000000000000000000000 : ℝ)*base80 + (2508230974547/42312500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (53479/40000000000000000000 : ℝ)*base89 + (53479/40000000000000000000 : ℝ)*base91 + (53479/40000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1129_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193761/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14043/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2267/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11337/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14041/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1129_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1129_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193761/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (353/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11337/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14041/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1129_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1129_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1129_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193761/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (353/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11337/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14041/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1129_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
