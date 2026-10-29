-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1401_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:45:30.353255+00:00
-- url     : https://prove2.me/submissions/4b3b3013-3e6b-4915-af38-64e5fa714635

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
theorem support_rectangle_w1401_s6_0 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1994074811/10000000000 : ℝ)*x 0 + (5409667903/10000000000 : ℝ)*x 1 + (2623121123/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1994074811/10000000000 : ℝ)^4361 ≤ (2431579018277/20000000000000 : ℝ)^3337 := by
    have hnat : (1994074811 : ℕ)^4361*20000000000000^3337 ≤ 2431579018277^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1994074811 10000000000 2431579018277 20000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409667903/10000000000 : ℝ)^4361 ≤ (22400653424013/50000000000000 : ℝ)^3337 := by
    have hnat : (5409667903 : ℕ)^4361*50000000000000^3337 ≤ 22400653424013^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409667903 10000000000 22400653424013 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623121123/5000000000 : ℝ)^4361 ≤ (10760199512731/25000000000000 : ℝ)^3337 := by
    have hnat : (2623121123 : ℕ)^4361*25000000000000^3337 ≤ 10760199512731^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623121123 5000000000 10760199512731 25000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1994074811/10000000000 : ℝ), (5409667903/10000000000 : ℝ), (2623121123/5000000000 : ℝ)] ![(2431579018277/20000000000000 : ℝ), (22400653424013/50000000000000 : ℝ), (10760199512731/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1994074811/10000000000 : ℝ)|^4361 ≤ (2431579018277/20000000000000 : ℝ)^3337
        have hw : |(-1994074811/10000000000 : ℝ)|=(1994074811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409667903/10000000000 : ℝ)|^4361 ≤ (22400653424013/50000000000000 : ℝ)^3337
        have hw : |(5409667903/10000000000 : ℝ)|=(5409667903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623121123/5000000000 : ℝ)|^4361 ≤ (10760199512731/25000000000000 : ℝ)^3337
        have hw : |(2623121123/5000000000 : ℝ)|=(2623121123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s6_1 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347902321/10000000000 : ℝ)*x 0 + (-2077297233/10000000000 : ℝ)*x 1 + (655780279/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347902321/10000000000 : ℝ)^4361 ≤ (551674857477/1250000000000 : ℝ)^3337 := by
    have hnat : (5347902321 : ℕ)^4361*1250000000000^3337 ≤ 551674857477^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347902321 10000000000 551674857477 1250000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2077297233/10000000000 : ℝ)^4361 ≤ (12825213487469/100000000000000 : ℝ)^3337 := by
    have hnat : (2077297233 : ℕ)^4361*100000000000000^3337 ≤ 12825213487469^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077297233 10000000000 12825213487469 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655780279/1250000000 : ℝ)^4361 ≤ (43040797900821/100000000000000 : ℝ)^3337 := by
    have hnat : (655780279 : ℕ)^4361*100000000000000^3337 ≤ 43040797900821^3337*1250000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655780279 1250000000 43040797900821 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347902321/10000000000 : ℝ), (-2077297233/10000000000 : ℝ), (655780279/1250000000 : ℝ)] ![(551674857477/1250000000000 : ℝ), (12825213487469/100000000000000 : ℝ), (43040797900821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347902321/10000000000 : ℝ)|^4361 ≤ (551674857477/1250000000000 : ℝ)^3337
        have hw : |(5347902321/10000000000 : ℝ)|=(5347902321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2077297233/10000000000 : ℝ)|^4361 ≤ (12825213487469/100000000000000 : ℝ)^3337
        have hw : |(-2077297233/10000000000 : ℝ)|=(2077297233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655780279/1250000000 : ℝ)|^4361 ≤ (43040797900821/100000000000000 : ℝ)^3337
        have hw : |(655780279/1250000000 : ℝ)|=(655780279/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s6_2 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347902289/10000000000 : ℝ)*x 0 + (2623121131/5000000000 : ℝ)*x 1 + (-415459447/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347902289/10000000000 : ℝ)^4361 ≤ (44133988253041/100000000000000 : ℝ)^3337 := by
    have hnat : (5347902289 : ℕ)^4361*100000000000000^3337 ≤ 44133988253041^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347902289 10000000000 44133988253041 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623121131/5000000000 : ℝ)^4361 ≤ (43040798222471/100000000000000 : ℝ)^3337 := by
    have hnat : (2623121131 : ℕ)^4361*100000000000000^3337 ≤ 43040798222471^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623121131 5000000000 43040798222471 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (415459447/2000000000 : ℝ)^4361 ≤ (6412606751803/50000000000000 : ℝ)^3337 := by
    have hnat : (415459447 : ℕ)^4361*50000000000000^3337 ≤ 6412606751803^3337*2000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415459447 2000000000 6412606751803 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347902289/10000000000 : ℝ), (2623121131/5000000000 : ℝ), (-415459447/2000000000 : ℝ)] ![(44133988253041/100000000000000 : ℝ), (43040798222471/100000000000000 : ℝ), (6412606751803/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347902289/10000000000 : ℝ)|^4361 ≤ (44133988253041/100000000000000 : ℝ)^3337
        have hw : |(5347902289/10000000000 : ℝ)|=(5347902289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623121131/5000000000 : ℝ)|^4361 ≤ (43040798222471/100000000000000 : ℝ)^3337
        have hw : |(2623121131/5000000000 : ℝ)|=(2623121131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-415459447/2000000000 : ℝ)|^4361 ≤ (6412606751803/50000000000000 : ℝ)^3337
        have hw : |(-415459447/2000000000 : ℝ)|=(415459447/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s6_3 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2155712287/5000000000 : ℝ)*x 0 + (827939317/2000000000 : ℝ)*x 1 + (179584691/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155712287/5000000000 : ℝ)^4361 ≤ (6660849626191/20000000000000 : ℝ)^3337 := by
    have hnat : (2155712287 : ℕ)^4361*20000000000000^3337 ≤ 6660849626191^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155712287 5000000000 6660849626191 20000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (827939317/2000000000 : ℝ)^4361 ≤ (31581338273607/100000000000000 : ℝ)^3337 := by
    have hnat : (827939317 : ℕ)^4361*100000000000000^3337 ≤ 31581338273607^3337*2000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827939317 2000000000 31581338273607 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (179584691/400000000 : ℝ)^4361 ≤ (17557206788277/50000000000000 : ℝ)^3337 := by
    have hnat : (179584691 : ℕ)^4361*50000000000000^3337 ≤ 17557206788277^3337*400000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179584691 400000000 17557206788277 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2155712287/5000000000 : ℝ), (827939317/2000000000 : ℝ), (179584691/400000000 : ℝ)] ![(6660849626191/20000000000000 : ℝ), (31581338273607/100000000000000 : ℝ), (17557206788277/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2155712287/5000000000 : ℝ)|^4361 ≤ (6660849626191/20000000000000 : ℝ)^3337
        have hw : |(2155712287/5000000000 : ℝ)|=(2155712287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(827939317/2000000000 : ℝ)|^4361 ≤ (31581338273607/100000000000000 : ℝ)^3337
        have hw : |(827939317/2000000000 : ℝ)|=(827939317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(179584691/400000000 : ℝ)|^4361 ≤ (17557206788277/50000000000000 : ℝ)^3337
        have hw : |(179584691/400000000 : ℝ)|=(179584691/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s6_4 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1994086381/10000000000 : ℝ)*x 0 + (5246830257/10000000000 : ℝ)*x 1 + (5409076863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1994086381/10000000000 : ℝ)^4361 ≤ (1519748410087/12500000000000 : ℝ)^3337 := by
    have hnat : (1994086381 : ℕ)^4361*12500000000000^3337 ≤ 1519748410087^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1994086381 10000000000 1519748410087 12500000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246830257/10000000000 : ℝ)^4361 ≤ (21523551305401/50000000000000 : ℝ)^3337 := by
    have hnat : (5246830257 : ℕ)^4361*50000000000000^3337 ≤ 21523551305401^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246830257 10000000000 21523551305401 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409076863/10000000000 : ℝ)^4361 ≤ (1791796403819/4000000000000 : ℝ)^3337 := by
    have hnat : (5409076863 : ℕ)^4361*4000000000000^3337 ≤ 1791796403819^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409076863 10000000000 1791796403819 4000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1994086381/10000000000 : ℝ), (5246830257/10000000000 : ℝ), (5409076863/10000000000 : ℝ)] ![(1519748410087/12500000000000 : ℝ), (21523551305401/50000000000000 : ℝ), (1791796403819/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1994086381/10000000000 : ℝ)|^4361 ≤ (1519748410087/12500000000000 : ℝ)^3337
        have hw : |(-1994086381/10000000000 : ℝ)|=(1994086381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246830257/10000000000 : ℝ)|^4361 ≤ (21523551305401/50000000000000 : ℝ)^3337
        have hw : |(5246830257/10000000000 : ℝ)|=(5246830257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409076863/10000000000 : ℝ)|^4361 ≤ (1791796403819/4000000000000 : ℝ)^3337
        have hw : |(5409076863/10000000000 : ℝ)|=(5409076863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s6_5 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305535429/10000000000 : ℝ)*x 0 + (-1914462641/10000000000 : ℝ)*x 1 + (5409076863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305535429/10000000000 : ℝ)^4361 ≤ (43677618670683/100000000000000 : ℝ)^3337 := by
    have hnat : (5305535429 : ℕ)^4361*100000000000000^3337 ≤ 43677618670683^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305535429 10000000000 43677618670683 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1914462641/10000000000 : ℝ)^4361 ≤ (11527471215919/100000000000000 : ℝ)^3337 := by
    have hnat : (1914462641 : ℕ)^4361*100000000000000^3337 ≤ 11527471215919^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1914462641 10000000000 11527471215919 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409076863/10000000000 : ℝ)^4361 ≤ (1791796403819/4000000000000 : ℝ)^3337 := by
    have hnat : (5409076863 : ℕ)^4361*4000000000000^3337 ≤ 1791796403819^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409076863 10000000000 1791796403819 4000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305535429/10000000000 : ℝ), (-1914462641/10000000000 : ℝ), (5409076863/10000000000 : ℝ)] ![(43677618670683/100000000000000 : ℝ), (11527471215919/100000000000000 : ℝ), (1791796403819/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305535429/10000000000 : ℝ)|^4361 ≤ (43677618670683/100000000000000 : ℝ)^3337
        have hw : |(5305535429/10000000000 : ℝ)|=(5305535429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1914462641/10000000000 : ℝ)|^4361 ≤ (11527471215919/100000000000000 : ℝ)^3337
        have hw : |(-1914462641/10000000000 : ℝ)|=(1914462641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409076863/10000000000 : ℝ)|^4361 ≤ (1791796403819/4000000000000 : ℝ)^3337
        have hw : |(5409076863/10000000000 : ℝ)|=(5409076863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s6_6 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305535423/10000000000 : ℝ)*x 0 + (5409076869/10000000000 : ℝ)*x 1 + (-1914462641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305535423/10000000000 : ℝ)^4361 ≤ (43677618606131/100000000000000 : ℝ)^3337 := by
    have hnat : (5305535423 : ℕ)^4361*100000000000000^3337 ≤ 43677618606131^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305535423 10000000000 43677618606131 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409076869/10000000000 : ℝ)^4361 ≤ (44794910160411/100000000000000 : ℝ)^3337 := by
    have hnat : (5409076869 : ℕ)^4361*100000000000000^3337 ≤ 44794910160411^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409076869 10000000000 44794910160411 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1914462641/10000000000 : ℝ)^4361 ≤ (11527471215919/100000000000000 : ℝ)^3337 := by
    have hnat : (1914462641 : ℕ)^4361*100000000000000^3337 ≤ 11527471215919^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1914462641 10000000000 11527471215919 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305535423/10000000000 : ℝ), (5409076869/10000000000 : ℝ), (-1914462641/10000000000 : ℝ)] ![(43677618606131/100000000000000 : ℝ), (44794910160411/100000000000000 : ℝ), (11527471215919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305535423/10000000000 : ℝ)|^4361 ≤ (43677618606131/100000000000000 : ℝ)^3337
        have hw : |(5305535423/10000000000 : ℝ)|=(5305535423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409076869/10000000000 : ℝ)|^4361 ≤ (44794910160411/100000000000000 : ℝ)^3337
        have hw : |(5409076869/10000000000 : ℝ)|=(5409076869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1914462641/10000000000 : ℝ)|^4361 ≤ (11527471215919/100000000000000 : ℝ)^3337
        have hw : |(-1914462641/10000000000 : ℝ)|=(1914462641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s6_7 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2155724687/5000000000 : ℝ)*x 0 + (2244179131/5000000000 : ℝ)*x 1 + (1035240529/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155724687/5000000000 : ℝ)^4361 ≤ (16652249244279/50000000000000 : ℝ)^3337 := by
    have hnat : (2155724687 : ℕ)^4361*50000000000000^3337 ≤ 16652249244279^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155724687 5000000000 16652249244279 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2244179131/5000000000 : ℝ)^4361 ≤ (17550772692661/50000000000000 : ℝ)^3337 := by
    have hnat : (2244179131 : ℕ)^4361*50000000000000^3337 ≤ 17550772692661^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244179131 5000000000 17550772692661 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035240529/2500000000 : ℝ)^4361 ≤ (15796978057369/50000000000000 : ℝ)^3337 := by
    have hnat : (1035240529 : ℕ)^4361*50000000000000^3337 ≤ 15796978057369^3337*2500000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035240529 2500000000 15796978057369 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2155724687/5000000000 : ℝ), (2244179131/5000000000 : ℝ), (1035240529/2500000000 : ℝ)] ![(16652249244279/50000000000000 : ℝ), (17550772692661/50000000000000 : ℝ), (15796978057369/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2155724687/5000000000 : ℝ)|^4361 ≤ (16652249244279/50000000000000 : ℝ)^3337
        have hw : |(2155724687/5000000000 : ℝ)|=(2155724687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2244179131/5000000000 : ℝ)|^4361 ≤ (17550772692661/50000000000000 : ℝ)^3337
        have hw : |(2244179131/5000000000 : ℝ)|=(2244179131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1035240529/2500000000 : ℝ)|^4361 ≤ (15796978057369/50000000000000 : ℝ)^3337
        have hw : |(1035240529/2500000000 : ℝ)|=(1035240529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1401_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157058059/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14747/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11277/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11281/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7371/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14747/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11277/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14747/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11277/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14747/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11277/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14747/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11277/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14747/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11277/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14747/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11277/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11277/100000 : ℝ) ^ (545/128 : ℝ) ≤ (2303339672266501/25000000000000000000 : ℝ) := by
    have hpowers : (11277/100000 : ℝ)^545 ≤ (2303339672266501/25000000000000000000 : ℝ)^128 := by
      have hnat : (11277 : ℕ)^545*25000000000000000000^128 ≤ 2303339672266501^128*100000^545 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11277 100000 2303339672266501 25000000000000000000 545 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11277/100000 : ℝ)) (X := (2303339672266501/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14747/100000 : ℝ) ^ (545/128 : ℝ) ≤ (28873281069946297/100000000000000000000 : ℝ) := by
    have hpowers : (14747/100000 : ℝ)^545 ≤ (28873281069946297/100000000000000000000 : ℝ)^128 := by
      have hnat : (14747 : ℕ)^545*100000000000000000000^128 ≤ 28873281069946297^128*100000^545 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14747 100000 28873281069946297 100000000000000000000 545 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14747/100000 : ℝ)) (X := (28873281069946297/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502303339672266501/12500000000000000000 : ℝ) ≤ (10000432743774647/10000000000000000 : ℝ) ^ (545/128 : ℝ) := by
    have hpowers : (12502303339672266501/12500000000000000000 : ℝ)^128 ≤ (10000432743774647/10000000000000000 : ℝ)^545 := by
      have hnat : (12502303339672266501 : ℕ)^128*10000000000000000^545 ≤ 10000432743774647^545*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502303339672266501 12500000000000000000 10000432743774647 10000000000000000 128 545 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000432743774647/10000000000000000 : ℝ)) (X := (12502303339672266501/12500000000000000000 : ℝ)) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038086639759012301/100000000000000000000 : ℝ) ≤ (10000894381598281/10000000000000000 : ℝ) ^ (545/128 : ℝ) := by
    have hpowers : (100038086639759012301/100000000000000000000 : ℝ)^128 ≤ (10000894381598281/10000000000000000 : ℝ)^545 := by
      have hnat : (100038086639759012301 : ℕ)^128*10000000000000000^545 ≤ 10000894381598281^545*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038086639759012301 100000000000000000000 10000894381598281 10000000000000000 128 545 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000894381598281/10000000000000000 : ℝ)) (X := (100038086639759012301/100000000000000000000 : ℝ)) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028873281069946297/50000000000000000000 : ℝ) ≤ (2000271203884383/2000000000000000 : ℝ) ^ (545/128 : ℝ) := by
    have hpowers : (50028873281069946297/50000000000000000000 : ℝ)^128 ≤ (2000271203884383/2000000000000000 : ℝ)^545 := by
      have hnat : (50028873281069946297 : ℕ)^128*2000000000000000^545 ≤ 2000271203884383^545*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028873281069946297 50000000000000000000 2000271203884383 2000000000000000 128 545 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000271203884383/2000000000000000 : ℝ)) (X := (50028873281069946297/50000000000000000000 : ℝ)) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2303339672266501/25000000000000000000 : ℝ) ≤ ((17345544920711891927/17350000000000000000 : ℝ)+2*(230818911817/173500000000000 : ℝ)*(11277/100000 : ℝ))^(545/128 : ℝ) := by
    rw [show (17345544920711891927/17350000000000000000 : ℝ)+2*(230818911817/173500000000000 : ℝ)*(11277/100000 : ℝ)=(10000432743774647/10000000000000000 : ℝ) by norm_num, show 1+2*(2303339672266501/25000000000000000000 : ℝ)=(12502303339672266501/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28873281069946297/100000000000000000000 : ℝ)+(2303339672266501/25000000000000000000 : ℝ) ≤ ((17345544920711891927/17350000000000000000 : ℝ)+(230818911817/173500000000000 : ℝ)*((14747/100000 : ℝ)+(11277/100000 : ℝ)))^(545/128 : ℝ) := by
    rw [show (17345544920711891927/17350000000000000000 : ℝ)+(230818911817/173500000000000 : ℝ)*((14747/100000 : ℝ)+(11277/100000 : ℝ))=(10000894381598281/10000000000000000 : ℝ) by norm_num, show 1+(28873281069946297/100000000000000000000 : ℝ)+(2303339672266501/25000000000000000000 : ℝ)=(100038086639759012301/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28873281069946297/100000000000000000000 : ℝ) ≤ ((17345544920711891927/17350000000000000000 : ℝ)+2*(230818911817/173500000000000 : ℝ)*(14747/100000 : ℝ))^(545/128 : ℝ) := by
    rw [show (17345544920711891927/17350000000000000000 : ℝ)+2*(230818911817/173500000000000 : ℝ)*(14747/100000 : ℝ)=(2000271203884383/2000000000000000 : ℝ) by norm_num, show 1+2*(28873281069946297/100000000000000000000 : ℝ)=(50028873281069946297/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17345544920711891927/17350000000000000000 : ℝ)*(X 1 0+X 2 0)+(230818911817/173500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (545/128 : ℝ)) (lo := (11277/100000 : ℝ)) (hi := (14747/100000 : ℝ)) (c := (17345544920711891927/17350000000000000000 : ℝ)) (alpha := (230818911817/173500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17345544920711891927/17350000000000000000 : ℝ)*(X 0 1+X 2 1)+(230818911817/173500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (545/128 : ℝ)) (lo := (11277/100000 : ℝ)) (hi := (14747/100000 : ℝ)) (c := (17345544920711891927/17350000000000000000 : ℝ)) (alpha := (230818911817/173500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17345544920711891927/17350000000000000000 : ℝ)*(X 0 2+X 1 2)+(230818911817/173500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (545/128 : ℝ)) (lo := (11277/100000 : ℝ)) (hi := (14747/100000 : ℝ)) (c := (17345544920711891927/17350000000000000000 : ℝ)) (alpha := (230818911817/173500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1994074811/10000000000 : ℝ)*X 0 0+(5409667903/10000000000 : ℝ)*X 0 1+(2623121123/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347902321/10000000000 : ℝ)*X 1 0+(-2077297233/10000000000 : ℝ)*X 1 1+(655780279/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347902289/10000000000 : ℝ)*X 2 0+(2623121131/5000000000 : ℝ)*X 2 1+(-415459447/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2155712287/5000000000 : ℝ)*X 0 0+(827939317/2000000000 : ℝ)*X 0 1+(179584691/400000000 : ℝ)*X 0 2+(2155712287/5000000000 : ℝ)*X 1 0+(827939317/2000000000 : ℝ)*X 1 1+(179584691/400000000 : ℝ)*X 1 2+(2155712287/5000000000 : ℝ)*X 2 0+(827939317/2000000000 : ℝ)*X 2 1+(179584691/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1994086381/10000000000 : ℝ)*X 0 0+(5246830257/10000000000 : ℝ)*X 0 1+(5409076863/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305535429/10000000000 : ℝ)*X 1 0+(-1914462641/10000000000 : ℝ)*X 1 1+(5409076863/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305535423/10000000000 : ℝ)*X 2 0+(5409076869/10000000000 : ℝ)*X 2 1+(-1914462641/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2155724687/5000000000 : ℝ)*X 0 0+(2244179131/5000000000 : ℝ)*X 0 1+(1035240529/2500000000 : ℝ)*X 0 2+(2155724687/5000000000 : ℝ)*X 1 0+(2244179131/5000000000 : ℝ)*X 1 1+(1035240529/2500000000 : ℝ)*X 1 2+(2155724687/5000000000 : ℝ)*X 2 0+(2244179131/5000000000 : ℝ)*X 2 1+(1035240529/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3878945858867228443420997109/433750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1750260753/100000000000000 : ℝ)*(base19) + (322213223/20000000000000 : ℝ)*(base23) + (54858929/100000000000000 : ℝ)*(lower2) + (229731183/100000000000000 : ℝ)*(upper3) + (72776279/50000000000000 : ℝ)*(upper5) + (4488445556464689/100000000000000 : ℝ)*(major0) + (4488445556464689/100000000000000 : ℝ)*(major1) + (448844555646469/10000000000000 : ℝ)*(major2) + (1223805732727991/20000000000000 : ℝ)*(sp0) + (1529765843938601/25000000000000 : ℝ)*(sp1) + (3059531757474521/50000000000000 : ℝ)*(sp2) + (11163309460341/390625000000 : ℝ)*(sp3) + (18231187601/50000000000000 : ℝ)*(sp4) + (18466973097/100000000000000 : ℝ)*(sp7) + (2857825688820393/100000000000000 : ℝ)*(f.failure) + (6119065126015157/100000000000000 : ℝ)*(f.sum) + (15407851416393/17350000000000000000000000000 : ℝ)*base65 + (19574210261022334297/1735000000000000000000000000000000 : ℝ)*base68 + (1106019805808285763/173500000000000000000000000000000 : ℝ)*base69 + (5092862753577334297/1735000000000000000000000000000000 : ℝ)*base72 + (65291366047057/17350000000000000000000000000 : ℝ)*base74 + (265861952583714237/173500000000000000000000000000000 : ℝ)*base76 + (14055680407449034297/1735000000000000000000000000000000 : ℝ)*base78 + (25261827245079034297/1735000000000000000000000000000000 : ℝ)*base80 + (25259603446063/8675000000000000000000000000 : ℝ)*base81 + (24197187/10000000000000000000000 : ℝ)*base89 + (24197187/10000000000000000000000 : ℝ)*base91 + (75802813/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (925066779853397485889608863/216875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (733858133/100000000000000 : ℝ)*(base19) + (398282783/50000000000000 : ℝ)*(base23) + (49934469/20000000000000 : ℝ)*(lower1) + (87236273/100000000000000 : ℝ)*(upper3) + (7859143/25000000000000 : ℝ)*(lower4) + (4269693/5000000000000 : ℝ)*(upper5) + (2260497950798923/50000000000000 : ℝ)*(major0) + (2260497950798923/50000000000000 : ℝ)*(major1) + (2260497950798923/50000000000000 : ℝ)*(major2) + (130553607/10000000000000 : ℝ)*(sp2) + (6163440932460053/100000000000000 : ℝ)*(sp4) + (6163440198601919/100000000000000 : ℝ)*(sp5) + (6163438830358417/100000000000000 : ℝ)*(sp6) + (1439275364277183/50000000000000 : ℝ)*(sp7) + (1439275364277183/50000000000000 : ℝ)*(f.failure) + (6163440932460053/100000000000000 : ℝ)*(f.sum) + (1063092748243/8675000000000000000000000000 : ℝ)*base66 + (10047787093734405379/867500000000000000000000000000000 : ℝ)*base68 + (8855370765369405379/867500000000000000000000000000000 : ℝ)*base70 + (32884215684180594621/867500000000000000000000000000000 : ℝ)*base71 + (8818847431593/8675000000000000000000000000 : ℝ)*base74 + (92704664480934405379/867500000000000000000000000000000 : ℝ)*base76 + (9434933904294405379/867500000000000000000000000000000 : ℝ)*base78 + (4712074876044405379/867500000000000000000000000000000 : ℝ)*base80 + (18069597604393/8675000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (32203/5000000000000000000000 : ℝ)*base90 + (32203/5000000000000000000000 : ℝ)*base92 + (32203/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1401_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157058059/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14747/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11277/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11281/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7371/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1401_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1401_s7_0 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-498520121/2500000000 : ℝ)*x 0 + (2704816319/5000000000 : ℝ)*x 1 + (1311568407/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (498520121/2500000000 : ℝ)^4361 ≤ (1519742536701/12500000000000 : ℝ)^3337 := by
    have hnat : (498520121 : ℕ)^4361*12500000000000^3337 ≤ 1519742536701^3337*2500000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      498520121 2500000000 1519742536701 12500000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704816319/5000000000 : ℝ)^4361 ≤ (44800925173293/100000000000000 : ℝ)^3337 := by
    have hnat : (2704816319 : ℕ)^4361*100000000000000^3337 ≤ 44800925173293^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704816319 5000000000 44800925173293 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311568407/2500000000 : ℝ)^4361 ≤ (43041134518231/100000000000000 : ℝ)^3337 := by
    have hnat : (1311568407 : ℕ)^4361*100000000000000^3337 ≤ 43041134518231^3337*2500000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311568407 2500000000 43041134518231 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-498520121/2500000000 : ℝ), (2704816319/5000000000 : ℝ), (1311568407/2500000000 : ℝ)] ![(1519742536701/12500000000000 : ℝ), (44800925173293/100000000000000 : ℝ), (43041134518231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-498520121/2500000000 : ℝ)|^4361 ≤ (1519742536701/12500000000000 : ℝ)^3337
        have hw : |(-498520121/2500000000 : ℝ)|=(498520121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704816319/5000000000 : ℝ)|^4361 ≤ (44800925173293/100000000000000 : ℝ)^3337
        have hw : |(2704816319/5000000000 : ℝ)|=(2704816319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311568407/2500000000 : ℝ)|^4361 ≤ (43041134518231/100000000000000 : ℝ)^3337
        have hw : |(1311568407/2500000000 : ℝ)|=(1311568407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s7_1 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336973249/2500000000 : ℝ)*x 0 + (-2077268629/10000000000 : ℝ)*x 1 + (2623136569/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336973249/2500000000 : ℝ)^4361 ≤ (44133888028191/100000000000000 : ℝ)^3337 := by
    have hnat : (1336973249 : ℕ)^4361*100000000000000^3337 ≤ 44133888028191^3337*2500000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336973249 2500000000 44133888028191 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2077268629/10000000000 : ℝ)^4361 ≤ (1603122836871/12500000000000 : ℝ)^3337 := by
    have hnat : (2077268629 : ℕ)^4361*12500000000000^3337 ≤ 1603122836871^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077268629 10000000000 1603122836871 12500000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623136569/5000000000 : ℝ)^4361 ≤ (4304112926461/10000000000000 : ℝ)^3337 := by
    have hnat : (2623136569 : ℕ)^4361*10000000000000^3337 ≤ 4304112926461^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623136569 5000000000 4304112926461 10000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336973249/2500000000 : ℝ), (-2077268629/10000000000 : ℝ), (2623136569/5000000000 : ℝ)] ![(44133888028191/100000000000000 : ℝ), (1603122836871/12500000000000 : ℝ), (4304112926461/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336973249/2500000000 : ℝ)|^4361 ≤ (44133888028191/100000000000000 : ℝ)^3337
        have hw : |(1336973249/2500000000 : ℝ)|=(1336973249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2077268629/10000000000 : ℝ)|^4361 ≤ (1603122836871/12500000000000 : ℝ)^3337
        have hw : |(-2077268629/10000000000 : ℝ)|=(2077268629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623136569/5000000000 : ℝ)|^4361 ≤ (4304112926461/10000000000000 : ℝ)^3337
        have hw : |(2623136569/5000000000 : ℝ)|=(2623136569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s7_2 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347892599/10000000000 : ℝ)*x 0 + (2623136851/5000000000 : ℝ)*x 1 + (-2077268409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347892599/10000000000 : ℝ)^4361 ≤ (22066941873277/50000000000000 : ℝ)^3337 := by
    have hnat : (5347892599 : ℕ)^4361*50000000000000^3337 ≤ 22066941873277^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347892599 10000000000 22066941873277 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623136851/5000000000 : ℝ)^4361 ≤ (8608227062327/20000000000000 : ℝ)^3337 := by
    have hnat : (2623136851 : ℕ)^4361*20000000000000^3337 ≤ 8608227062327^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623136851 5000000000 8608227062327 20000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2077268409/10000000000 : ℝ)^4361 ≤ (6412490459947/50000000000000 : ℝ)^3337 := by
    have hnat : (2077268409 : ℕ)^4361*50000000000000^3337 ≤ 6412490459947^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077268409 10000000000 6412490459947 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347892599/10000000000 : ℝ), (2623136851/5000000000 : ℝ), (-2077268409/10000000000 : ℝ)] ![(22066941873277/50000000000000 : ℝ), (8608227062327/20000000000000 : ℝ), (6412490459947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347892599/10000000000 : ℝ)|^4361 ≤ (22066941873277/50000000000000 : ℝ)^3337
        have hw : |(5347892599/10000000000 : ℝ)|=(5347892599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623136851/5000000000 : ℝ)|^4361 ≤ (8608227062327/20000000000000 : ℝ)^3337
        have hw : |(2623136851/5000000000 : ℝ)|=(2623136851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2077268409/10000000000 : ℝ)|^4361 ≤ (6412490459947/50000000000000 : ℝ)^3337
        have hw : |(-2077268409/10000000000 : ℝ)|=(2077268409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s7_3 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4311426821/10000000000 : ℝ)*x 0 + (2069883643/5000000000 : ℝ)*x 1 + (4489546093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4311426821/10000000000 : ℝ)^4361 ≤ (33304270814547/100000000000000 : ℝ)^3337 := by
    have hnat : (4311426821 : ℕ)^4361*100000000000000^3337 ≤ 33304270814547^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4311426821 10000000000 33304270814547 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2069883643/5000000000 : ℝ)^4361 ≤ (31582043159133/100000000000000 : ℝ)^3337 := by
    have hnat : (2069883643 : ℕ)^4361*100000000000000^3337 ≤ 31582043159133^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069883643 5000000000 31582043159133 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4489546093/10000000000 : ℝ)^4361 ≤ (35113686006009/100000000000000 : ℝ)^3337 := by
    have hnat : (4489546093 : ℕ)^4361*100000000000000^3337 ≤ 35113686006009^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489546093 10000000000 35113686006009 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4311426821/10000000000 : ℝ), (2069883643/5000000000 : ℝ), (4489546093/10000000000 : ℝ)] ![(33304270814547/100000000000000 : ℝ), (31582043159133/100000000000000 : ℝ), (35113686006009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4311426821/10000000000 : ℝ)|^4361 ≤ (33304270814547/100000000000000 : ℝ)^3337
        have hw : |(4311426821/10000000000 : ℝ)|=(4311426821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2069883643/5000000000 : ℝ)|^4361 ≤ (31582043159133/100000000000000 : ℝ)^3337
        have hw : |(2069883643/5000000000 : ℝ)|=(2069883643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4489546093/10000000000 : ℝ)|^4361 ≤ (35113686006009/100000000000000 : ℝ)^3337
        have hw : |(4489546093/10000000000 : ℝ)|=(4489546093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s7_4 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1994091837/10000000000 : ℝ)*x 0 + (5246860983/10000000000 : ℝ)*x 1 + (1081808481/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1994091837/10000000000 : ℝ)^4361 ≤ (12158030753949/100000000000000 : ℝ)^3337 := by
    have hnat : (1994091837 : ℕ)^4361*100000000000000^3337 ≤ 12158030753949^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1994091837 10000000000 12158030753949 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246860983/10000000000 : ℝ)^4361 ≤ (2152371602801/5000000000000 : ℝ)^3337 := by
    have hnat : (5246860983 : ℕ)^4361*5000000000000^3337 ≤ 2152371602801^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246860983 10000000000 2152371602801 5000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081808481/2000000000 : ℝ)^4361 ≤ (8958907433487/20000000000000 : ℝ)^3337 := by
    have hnat : (1081808481 : ℕ)^4361*20000000000000^3337 ≤ 8958907433487^3337*2000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081808481 2000000000 8958907433487 20000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1994091837/10000000000 : ℝ), (5246860983/10000000000 : ℝ), (1081808481/2000000000 : ℝ)] ![(12158030753949/100000000000000 : ℝ), (2152371602801/5000000000000 : ℝ), (8958907433487/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1994091837/10000000000 : ℝ)|^4361 ≤ (12158030753949/100000000000000 : ℝ)^3337
        have hw : |(-1994091837/10000000000 : ℝ)|=(1994091837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246860983/10000000000 : ℝ)|^4361 ≤ (2152371602801/5000000000000 : ℝ)^3337
        have hw : |(5246860983/10000000000 : ℝ)|=(5246860983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081808481/2000000000 : ℝ)|^4361 ≤ (8958907433487/20000000000000 : ℝ)^3337
        have hw : |(1081808481/2000000000 : ℝ)|=(1081808481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s7_5 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4311451279/10000000000 : ℝ)*x 0 + (28051803/62500000 : ℝ)*x 1 + (828206343/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4311451279/10000000000 : ℝ)^4361 ≤ (16652258859837/50000000000000 : ℝ)^3337 := by
    have hnat : (4311451279 : ℕ)^4361*50000000000000^3337 ≤ 16652258859837^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4311451279 10000000000 16652258859837 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (28051803/62500000 : ℝ)^4361 ≤ (17550416092953/50000000000000 : ℝ)^3337 := by
    have hnat : (28051803 : ℕ)^4361*50000000000000^3337 ≤ 17550416092953^3337*62500000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28051803 62500000 17550416092953 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (828206343/2000000000 : ℝ)^4361 ≤ (7898662519609/25000000000000 : ℝ)^3337 := by
    have hnat : (828206343 : ℕ)^4361*25000000000000^3337 ≤ 7898662519609^3337*2000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828206343 2000000000 7898662519609 25000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4311451279/10000000000 : ℝ), (28051803/62500000 : ℝ), (828206343/2000000000 : ℝ)] ![(16652258859837/50000000000000 : ℝ), (17550416092953/50000000000000 : ℝ), (7898662519609/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4311451279/10000000000 : ℝ)|^4361 ≤ (16652258859837/50000000000000 : ℝ)^3337
        have hw : |(4311451279/10000000000 : ℝ)|=(4311451279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(28051803/62500000 : ℝ)|^4361 ≤ (17550416092953/50000000000000 : ℝ)^3337
        have hw : |(28051803/62500000 : ℝ)|=(28051803/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(828206343/2000000000 : ℝ)|^4361 ≤ (7898662519609/25000000000000 : ℝ)^3337
        have hw : |(828206343/2000000000 : ℝ)|=(828206343/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1401_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157058059/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7371/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11281/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5641/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7371/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7371/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11281/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7371/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11281/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7371/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11281/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7371/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11281/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7371/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11281/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7371/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11281/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11281/100000 : ℝ) ^ (545/128 : ℝ) ≤ (2306820334271799/25000000000000000000 : ℝ) := by
    have hpowers : (11281/100000 : ℝ)^545 ≤ (2306820334271799/25000000000000000000 : ℝ)^128 := by
      have hnat : (11281 : ℕ)^545*25000000000000000000^128 ≤ 2306820334271799^128*100000^545 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11281 100000 2306820334271799 25000000000000000000 545 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11281/100000 : ℝ)) (X := (2306820334271799/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have hpowhi : (7371/50000 : ℝ) ^ (545/128 : ℝ) ≤ (7207905510397087/25000000000000000000 : ℝ) := by
    have hpowers : (7371/50000 : ℝ)^545 ≤ (7207905510397087/25000000000000000000 : ℝ)^128 := by
      have hnat : (7371 : ℕ)^545*25000000000000000000^128 ≤ 7207905510397087^128*50000^545 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7371 50000 7207905510397087 25000000000000000000 545 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7371/50000 : ℝ)) (X := (7207905510397087/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502306820334271799/12500000000000000000 : ℝ) ≤ (2500108349415913/2500000000000000 : ℝ) ^ (545/128 : ℝ) := by
    have hpowers : (12502306820334271799/12500000000000000000 : ℝ)^128 ≤ (2500108349415913/2500000000000000 : ℝ)^545 := by
      have hnat : (12502306820334271799 : ℕ)^128*2500000000000000^545 ≤ 2500108349415913^545*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502306820334271799 12500000000000000000 2500108349415913 2500000000000000 128 545 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500108349415913/2500000000000000 : ℝ)) (X := (12502306820334271799/12500000000000000000 : ℝ)) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (12504757362922334443/12500000000000000000 : ℝ) ≤ (5000446865182369/5000000000000000 : ℝ) ^ (545/128 : ℝ) := by
    have hpowers : (12504757362922334443/12500000000000000000 : ℝ)^128 ≤ (5000446865182369/5000000000000000 : ℝ)^545 := by
      have hnat : (12504757362922334443 : ℕ)^128*5000000000000000^545 ≤ 5000446865182369^545*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504757362922334443 12500000000000000000 5000446865182369 5000000000000000 128 545 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000446865182369/5000000000000000 : ℝ)) (X := (12504757362922334443/12500000000000000000 : ℝ)) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507207905510397087/12500000000000000000 : ℝ) ≤ (312542314470807/312500000000000 : ℝ) ^ (545/128 : ℝ) := by
    have hpowers : (12507207905510397087/12500000000000000000 : ℝ)^128 ≤ (312542314470807/312500000000000 : ℝ)^545 := by
      have hnat : (12507207905510397087 : ℕ)^128*312500000000000^545 ≤ 312542314470807^545*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507207905510397087 12500000000000000000 312542314470807 312500000000000 128 545 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312542314470807/312500000000000 : ℝ)) (X := (12507207905510397087/12500000000000000000 : ℝ)) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2306820334271799/25000000000000000000 : ℝ) ≤ ((865027849072799931/865250000000000000 : ℝ)+2*(230166350543/173050000000000 : ℝ)*(11281/100000 : ℝ))^(545/128 : ℝ) := by
    rw [show (865027849072799931/865250000000000000 : ℝ)+2*(230166350543/173050000000000 : ℝ)*(11281/100000 : ℝ)=(2500108349415913/2500000000000000 : ℝ) by norm_num, show 1+2*(2306820334271799/25000000000000000000 : ℝ)=(12502306820334271799/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7207905510397087/25000000000000000000 : ℝ)+(2306820334271799/25000000000000000000 : ℝ) ≤ ((865027849072799931/865250000000000000 : ℝ)+(230166350543/173050000000000 : ℝ)*((7371/50000 : ℝ)+(11281/100000 : ℝ)))^(545/128 : ℝ) := by
    rw [show (865027849072799931/865250000000000000 : ℝ)+(230166350543/173050000000000 : ℝ)*((7371/50000 : ℝ)+(11281/100000 : ℝ))=(5000446865182369/5000000000000000 : ℝ) by norm_num, show 1+(7207905510397087/25000000000000000000 : ℝ)+(2306820334271799/25000000000000000000 : ℝ)=(12504757362922334443/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7207905510397087/25000000000000000000 : ℝ) ≤ ((865027849072799931/865250000000000000 : ℝ)+2*(230166350543/173050000000000 : ℝ)*(7371/50000 : ℝ))^(545/128 : ℝ) := by
    rw [show (865027849072799931/865250000000000000 : ℝ)+2*(230166350543/173050000000000 : ℝ)*(7371/50000 : ℝ)=(312542314470807/312500000000000 : ℝ) by norm_num, show 1+2*(7207905510397087/25000000000000000000 : ℝ)=(12507207905510397087/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (865027849072799931/865250000000000000 : ℝ)*(X 1 0+X 2 0)+(230166350543/173050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (545/128 : ℝ)) (lo := (11281/100000 : ℝ)) (hi := (7371/50000 : ℝ)) (c := (865027849072799931/865250000000000000 : ℝ)) (alpha := (230166350543/173050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (865027849072799931/865250000000000000 : ℝ)*(X 0 1+X 2 1)+(230166350543/173050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (545/128 : ℝ)) (lo := (11281/100000 : ℝ)) (hi := (7371/50000 : ℝ)) (c := (865027849072799931/865250000000000000 : ℝ)) (alpha := (230166350543/173050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (865027849072799931/865250000000000000 : ℝ)*(X 0 2+X 1 2)+(230166350543/173050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (545/128 : ℝ)) (lo := (11281/100000 : ℝ)) (hi := (7371/50000 : ℝ)) (c := (865027849072799931/865250000000000000 : ℝ)) (alpha := (230166350543/173050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-498520121/2500000000 : ℝ)*X 0 0+(2704816319/5000000000 : ℝ)*X 0 1+(1311568407/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336973249/2500000000 : ℝ)*X 1 0+(-2077268629/10000000000 : ℝ)*X 1 1+(2623136569/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347892599/10000000000 : ℝ)*X 2 0+(2623136851/5000000000 : ℝ)*X 2 1+(-2077268409/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4311426821/10000000000 : ℝ)*X 0 0+(2069883643/5000000000 : ℝ)*X 0 1+(4489546093/10000000000 : ℝ)*X 0 2+(4311426821/10000000000 : ℝ)*X 1 0+(2069883643/5000000000 : ℝ)*X 1 1+(4489546093/10000000000 : ℝ)*X 1 2+(4311426821/10000000000 : ℝ)*X 2 0+(2069883643/5000000000 : ℝ)*X 2 1+(4489546093/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1994091837/10000000000 : ℝ)*X 0 0+(5246860983/10000000000 : ℝ)*X 0 1+(1081808481/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4311451279/10000000000 : ℝ)*X 0 0+(28051803/62500000 : ℝ)*X 0 1+(828206343/2000000000 : ℝ)*X 0 2+(4311451279/10000000000 : ℝ)*X 1 0+(28051803/62500000 : ℝ)*X 1 1+(828206343/2000000000 : ℝ)*X 1 2+(4311451279/10000000000 : ℝ)*X 2 0+(28051803/62500000 : ℝ)*X 2 1+(828206343/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s7_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24051126554140168661283549/4326250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (136920901/10000000000000 : ℝ)*(base19) + (228210449/25000000000000 : ℝ)*(base23) + (2612917/25000000000000 : ℝ)*(upper3) + (129479/12500000000000 : ℝ)*(upper4) + (207894587/100000000000000 : ℝ)*(upper5) + (449024918307193/10000000000000 : ℝ)*(major0) + (449024918307193/10000000000000 : ℝ)*(major1) + (449024918307193/10000000000000 : ℝ)*(major2) + (6121503192023101/100000000000000 : ℝ)*(sp0) + (3060761370360643/50000000000000 : ℝ)*(sp1) + (12243046394177/200000000000 : ℝ)*(sp2) + (2858964079915969/100000000000000 : ℝ)*(sp3) + (5229476799/25000000000000 : ℝ)*(sp4) + (9990986009/100000000000000 : ℝ)*(sp5) + (1429487035450989/50000000000000 : ℝ)*(f.failure) + (765190513741287/12500000000000 : ℝ)*(f.sum) + (1010653871623/216312500000000000000000000 : ℝ)*base66 + (22800853204201317/8652500000000000000000000000000 : ℝ)*base68 + (157451843851201317/8652500000000000000000000000000 : ℝ)*base70 + (59505643839491317/8652500000000000000000000000000 : ℝ)*base72 + (5420257395991/865250000000000000000000000 : ℝ)*base74 + (17978557018148683/8652500000000000000000000000000 : ℝ)*base75 + (43156733356701317/8652500000000000000000000000000 : ℝ)*base78 + (69004569455463683/8652500000000000000000000000000 : ℝ)*base79 + (1007579946847/432625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (21970351/5000000000000000000000 : ℝ)*base89 + (21970351/5000000000000000000000 : ℝ)*base91 + (21970351/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1401_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157058059/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7371/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11281/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5641/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7371/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1401_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1401_s8_0 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347892281/10000000000 : ℝ)*x 0 + (1311569557/2500000000 : ℝ)*x 1 + (-2077262821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347892281/10000000000 : ℝ)^4361 ≤ (4413388031693/10000000000000 : ℝ)^3337 := by
    have hnat : (5347892281 : ℕ)^4361*10000000000000^3337 ≤ 4413388031693^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347892281 10000000000 4413388031693 10000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311569557/2500000000 : ℝ)^4361 ≤ (5380147979743/12500000000000 : ℝ)^3337 := by
    have hnat : (1311569557 : ℕ)^4361*12500000000000^3337 ≤ 5380147979743^3337*2500000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311569557 2500000000 5380147979743 12500000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2077262821/10000000000 : ℝ)^4361 ≤ (12824935833011/100000000000000 : ℝ)^3337 := by
    have hnat : (2077262821 : ℕ)^4361*100000000000000^3337 ≤ 12824935833011^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077262821 10000000000 12824935833011 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347892281/10000000000 : ℝ), (1311569557/2500000000 : ℝ), (-2077262821/10000000000 : ℝ)] ![(4413388031693/10000000000000 : ℝ), (5380147979743/12500000000000 : ℝ), (12824935833011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347892281/10000000000 : ℝ)|^4361 ≤ (4413388031693/10000000000000 : ℝ)^3337
        have hw : |(5347892281/10000000000 : ℝ)|=(5347892281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311569557/2500000000 : ℝ)|^4361 ≤ (5380147979743/12500000000000 : ℝ)^3337
        have hw : |(1311569557/2500000000 : ℝ)|=(1311569557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2077262821/10000000000 : ℝ)|^4361 ≤ (12824935833011/100000000000000 : ℝ)^3337
        have hw : |(-2077262821/10000000000 : ℝ)|=(2077262821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s8_1 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1994089969/10000000000 : ℝ)*x 0 + (2623432511/5000000000 : ℝ)*x 1 + (270451989/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1994089969/10000000000 : ℝ)^4361 ≤ (6079007934887/50000000000000 : ℝ)^3337 := by
    have hnat : (1994089969 : ℕ)^4361*50000000000000^3337 ≤ 6079007934887^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1994089969 10000000000 6079007934887 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623432511/5000000000 : ℝ)^4361 ≤ (1076186884059/2500000000000 : ℝ)^3337 := by
    have hnat : (2623432511 : ℕ)^4361*2500000000000^3337 ≤ 1076186884059^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623432511 5000000000 1076186884059 2500000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270451989/500000000 : ℝ)^4361 ≤ (279965679737/625000000000 : ℝ)^3337 := by
    have hnat : (270451989 : ℕ)^4361*625000000000^3337 ≤ 279965679737^3337*500000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270451989 500000000 279965679737 625000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1994089969/10000000000 : ℝ), (2623432511/5000000000 : ℝ), (270451989/500000000 : ℝ)] ![(6079007934887/50000000000000 : ℝ), (1076186884059/2500000000000 : ℝ), (279965679737/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1994089969/10000000000 : ℝ)|^4361 ≤ (6079007934887/50000000000000 : ℝ)^3337
        have hw : |(-1994089969/10000000000 : ℝ)|=(1994089969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623432511/5000000000 : ℝ)|^4361 ≤ (1076186884059/2500000000000 : ℝ)^3337
        have hw : |(2623432511/5000000000 : ℝ)|=(2623432511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270451989/500000000 : ℝ)|^4361 ≤ (279965679737/625000000000 : ℝ)^3337
        have hw : |(270451989/500000000 : ℝ)|=(270451989/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s8_2 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305544803/10000000000 : ℝ)*x 0 + (-1914500823/10000000000 : ℝ)*x 1 + (5409039783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305544803/10000000000 : ℝ)^4361 ≤ (21838859761361/50000000000000 : ℝ)^3337 := by
    have hnat : (5305544803 : ℕ)^4361*50000000000000^3337 ≤ 21838859761361^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305544803 10000000000 21838859761361 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1914500823/10000000000 : ℝ)^4361 ≤ (11527771669257/100000000000000 : ℝ)^3337 := by
    have hnat : (1914500823 : ℕ)^4361*100000000000000^3337 ≤ 11527771669257^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1914500823 10000000000 11527771669257 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409039783/10000000000 : ℝ)^4361 ≤ (11198627197597/25000000000000 : ℝ)^3337 := by
    have hnat : (5409039783 : ℕ)^4361*25000000000000^3337 ≤ 11198627197597^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409039783 10000000000 11198627197597 25000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305544803/10000000000 : ℝ), (-1914500823/10000000000 : ℝ), (5409039783/10000000000 : ℝ)] ![(21838859761361/50000000000000 : ℝ), (11527771669257/100000000000000 : ℝ), (11198627197597/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305544803/10000000000 : ℝ)|^4361 ≤ (21838859761361/50000000000000 : ℝ)^3337
        have hw : |(5305544803/10000000000 : ℝ)|=(5305544803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1914500823/10000000000 : ℝ)|^4361 ≤ (11527771669257/100000000000000 : ℝ)^3337
        have hw : |(-1914500823/10000000000 : ℝ)|=(1914500823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409039783/10000000000 : ℝ)|^4361 ≤ (11198627197597/25000000000000 : ℝ)^3337
        have hw : |(5409039783/10000000000 : ℝ)|=(5409039783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s8_3 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061108961/2000000000 : ℝ)*x 0 + (2704519891/5000000000 : ℝ)*x 1 + (-957250411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061108961/2000000000 : ℝ)^4361 ≤ (43677719544239/100000000000000 : ℝ)^3337 := by
    have hnat : (1061108961 : ℕ)^4361*100000000000000^3337 ≤ 43677719544239^3337*2000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061108961 2000000000 43677719544239 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704519891/5000000000 : ℝ)^4361 ≤ (8958901755913/20000000000000 : ℝ)^3337 := by
    have hnat : (2704519891 : ℕ)^4361*20000000000000^3337 ≤ 8958901755913^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704519891 5000000000 8958901755913 20000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (957250411/5000000000 : ℝ)^4361 ≤ (2881942915347/25000000000000 : ℝ)^3337 := by
    have hnat : (957250411 : ℕ)^4361*25000000000000^3337 ≤ 2881942915347^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957250411 5000000000 2881942915347 25000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061108961/2000000000 : ℝ), (2704519891/5000000000 : ℝ), (-957250411/5000000000 : ℝ)] ![(43677719544239/100000000000000 : ℝ), (8958901755913/20000000000000 : ℝ), (2881942915347/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061108961/2000000000 : ℝ)|^4361 ≤ (43677719544239/100000000000000 : ℝ)^3337
        have hw : |(1061108961/2000000000 : ℝ)|=(1061108961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704519891/5000000000 : ℝ)|^4361 ≤ (8958901755913/20000000000000 : ℝ)^3337
        have hw : |(2704519891/5000000000 : ℝ)|=(2704519891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-957250411/5000000000 : ℝ)|^4361 ≤ (2881942915347/25000000000000 : ℝ)^3337
        have hw : |(-957250411/5000000000 : ℝ)|=(957250411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s8_4 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (538931489/1250000000 : ℝ)*x 0 + (561035127/1250000000 : ℝ)*x 1 + (1035259681/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538931489/1250000000 : ℝ)^4361 ≤ (33304524109857/100000000000000 : ℝ)^3337 := by
    have hnat : (538931489 : ℕ)^4361*100000000000000^3337 ≤ 33304524109857^3337*1250000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538931489 1250000000 33304524109857 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561035127/1250000000 : ℝ)^4361 ≤ (351007559011/1000000000000 : ℝ)^3337 := by
    have hnat : (561035127 : ℕ)^4361*1000000000000^3337 ≤ 351007559011^3337*1250000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561035127 1250000000 351007559011 1000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035259681/2500000000 : ℝ)^4361 ≤ (1263788798583/4000000000000 : ℝ)^3337 := by
    have hnat : (1035259681 : ℕ)^4361*4000000000000^3337 ≤ 1263788798583^3337*2500000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035259681 2500000000 1263788798583 4000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538931489/1250000000 : ℝ), (561035127/1250000000 : ℝ), (1035259681/2500000000 : ℝ)] ![(33304524109857/100000000000000 : ℝ), (351007559011/1000000000000 : ℝ), (1263788798583/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538931489/1250000000 : ℝ)|^4361 ≤ (33304524109857/100000000000000 : ℝ)^3337
        have hw : |(538931489/1250000000 : ℝ)|=(538931489/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(561035127/1250000000 : ℝ)|^4361 ≤ (351007559011/1000000000000 : ℝ)^3337
        have hw : |(561035127/1250000000 : ℝ)|=(561035127/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1035259681/2500000000 : ℝ)|^4361 ≤ (1263788798583/4000000000000 : ℝ)^3337
        have hw : |(1035259681/2500000000 : ℝ)|=(1035259681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1401_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157058059/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7371/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5641/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5641/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14741/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7371/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5641/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7371/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5641/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7371/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5641/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7371/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5641/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7371/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5641/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7371/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5641/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5641/50000 : ℝ) ^ (545/128 : ℝ) ≤ (4615382256485461/50000000000000000000 : ℝ) := by
    have hpowers : (5641/50000 : ℝ)^545 ≤ (4615382256485461/50000000000000000000 : ℝ)^128 := by
      have hnat : (5641 : ℕ)^545*50000000000000000000^128 ≤ 4615382256485461^128*50000^545 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5641 50000 4615382256485461 50000000000000000000 545 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5641/50000 : ℝ)) (X := (4615382256485461/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have hpowhi : (7371/50000 : ℝ) ^ (545/128 : ℝ) ≤ (7207905510397087/25000000000000000000 : ℝ) := by
    have hpowers : (7371/50000 : ℝ)^545 ≤ (7207905510397087/25000000000000000000 : ℝ)^128 := by
      have hnat : (7371 : ℕ)^545*25000000000000000000^128 ≤ 7207905510397087^128*50000^545 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7371 50000 7207905510397087 25000000000000000000 545 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7371/50000 : ℝ)) (X := (7207905510397087/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004615382256485461/25000000000000000000 : ℝ) ≤ (2500108390313487/2500000000000000 : ℝ) ^ (545/128 : ℝ) := by
    have hpowers : (25004615382256485461/25000000000000000000 : ℝ)^128 ≤ (2500108390313487/2500000000000000 : ℝ)^545 := by
      have hnat : (25004615382256485461 : ℕ)^128*2500000000000000^545 ≤ 2500108390313487^545*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004615382256485461 25000000000000000000 2500108390313487 2500000000000000 128 545 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500108390313487/2500000000000000 : ℝ)) (X := (25004615382256485461/25000000000000000000 : ℝ)) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (10003806238655455927/10000000000000000000 : ℝ) ≤ (10000893812147623/10000000000000000 : ℝ) ^ (545/128 : ℝ) := by
    have hpowers : (10003806238655455927/10000000000000000000 : ℝ)^128 ≤ (10000893812147623/10000000000000000 : ℝ)^545 := by
      have hnat : (10003806238655455927 : ℕ)^128*10000000000000000^545 ≤ 10000893812147623^545*10000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003806238655455927 10000000000000000000 10000893812147623 10000000000000000 128 545 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000893812147623/10000000000000000 : ℝ)) (X := (10003806238655455927/10000000000000000000 : ℝ)) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507207905510397087/12500000000000000000 : ℝ) ≤ (5000677031520649/5000000000000000 : ℝ) ^ (545/128 : ℝ) := by
    have hpowers : (12507207905510397087/12500000000000000000 : ℝ)^128 ≤ (5000677031520649/5000000000000000 : ℝ)^545 := by
      have hnat : (12507207905510397087 : ℕ)^128*5000000000000000^545 ≤ 5000677031520649^545*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507207905510397087 12500000000000000000 5000677031520649 5000000000000000 128 545 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000677031520649/5000000000000000 : ℝ)) (X := (12507207905510397087/12500000000000000000 : ℝ)) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4615382256485461/50000000000000000000 : ℝ) ≤ ((1729555751038688869/1730000000000000000 : ℝ)+2*(18410035747/13840000000000 : ℝ)*(5641/50000 : ℝ))^(545/128 : ℝ) := by
    rw [show (1729555751038688869/1730000000000000000 : ℝ)+2*(18410035747/13840000000000 : ℝ)*(5641/50000 : ℝ)=(2500108390313487/2500000000000000 : ℝ) by norm_num, show 1+2*(4615382256485461/50000000000000000000 : ℝ)=(25004615382256485461/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7207905510397087/25000000000000000000 : ℝ)+(4615382256485461/50000000000000000000 : ℝ) ≤ ((1729555751038688869/1730000000000000000 : ℝ)+(18410035747/13840000000000 : ℝ)*((7371/50000 : ℝ)+(5641/50000 : ℝ)))^(545/128 : ℝ) := by
    rw [show (1729555751038688869/1730000000000000000 : ℝ)+(18410035747/13840000000000 : ℝ)*((7371/50000 : ℝ)+(5641/50000 : ℝ))=(10000893812147623/10000000000000000 : ℝ) by norm_num, show 1+(7207905510397087/25000000000000000000 : ℝ)+(4615382256485461/50000000000000000000 : ℝ)=(10003806238655455927/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7207905510397087/25000000000000000000 : ℝ) ≤ ((1729555751038688869/1730000000000000000 : ℝ)+2*(18410035747/13840000000000 : ℝ)*(7371/50000 : ℝ))^(545/128 : ℝ) := by
    rw [show (1729555751038688869/1730000000000000000 : ℝ)+2*(18410035747/13840000000000 : ℝ)*(7371/50000 : ℝ)=(5000677031520649/5000000000000000 : ℝ) by norm_num, show 1+2*(7207905510397087/25000000000000000000 : ℝ)=(12507207905510397087/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1729555751038688869/1730000000000000000 : ℝ)*(X 1 0+X 2 0)+(18410035747/13840000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (545/128 : ℝ)) (lo := (5641/50000 : ℝ)) (hi := (7371/50000 : ℝ)) (c := (1729555751038688869/1730000000000000000 : ℝ)) (alpha := (18410035747/13840000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1729555751038688869/1730000000000000000 : ℝ)*(X 0 1+X 2 1)+(18410035747/13840000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (545/128 : ℝ)) (lo := (5641/50000 : ℝ)) (hi := (7371/50000 : ℝ)) (c := (1729555751038688869/1730000000000000000 : ℝ)) (alpha := (18410035747/13840000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1729555751038688869/1730000000000000000 : ℝ)*(X 0 2+X 1 2)+(18410035747/13840000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (545/128 : ℝ)) (lo := (5641/50000 : ℝ)) (hi := (7371/50000 : ℝ)) (c := (1729555751038688869/1730000000000000000 : ℝ)) (alpha := (18410035747/13840000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5347892281/10000000000 : ℝ)*X 2 0+(1311569557/2500000000 : ℝ)*X 2 1+(-2077262821/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s8_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-1994089969/10000000000 : ℝ)*X 0 0+(2623432511/5000000000 : ℝ)*X 0 1+(270451989/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s8_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5305544803/10000000000 : ℝ)*X 1 0+(-1914500823/10000000000 : ℝ)*X 1 1+(5409039783/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s8_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1061108961/2000000000 : ℝ)*X 2 0+(2704519891/5000000000 : ℝ)*X 2 1+(-957250411/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s8_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((538931489/1250000000 : ℝ)*X 0 0+(561035127/1250000000 : ℝ)*X 0 1+(1035259681/2500000000 : ℝ)*X 0 2+(538931489/1250000000 : ℝ)*X 1 0+(561035127/1250000000 : ℝ)*X 1 1+(1035259681/2500000000 : ℝ)*X 1 2+(538931489/1250000000 : ℝ)*X 2 0+(561035127/1250000000 : ℝ)*X 2 1+(1035259681/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s8_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22946407541545403385676191/10812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (92273319/25000000000000 : ℝ)*(base19) + (100851931/25000000000000 : ℝ)*(base23) + (15863737/12500000000000 : ℝ)*(lower1) + (5548651/12500000000000 : ℝ)*(upper3) + (3611029/25000000000000 : ℝ)*(lower4) + (9173019/20000000000000 : ℝ)*(upper5) + (1130751185859587/25000000000000 : ℝ)*(major0) + (1130751185859587/25000000000000 : ℝ)*(major1) + (1130751185859587/25000000000000 : ℝ)*(major2) + (597045499/100000000000000 : ℝ)*(sp0) + (1233235928695969/20000000000000 : ℝ)*(sp1) + (770772409298321/12500000000000 : ℝ)*(sp2) + (6166178643026621/100000000000000 : ℝ)*(sp3) + (2879829772656459/100000000000000 : ℝ)*(sp4) + (2879829772656459/100000000000000 : ℝ)*(f.failure) + (1233235928695969/20000000000000 : ℝ)*(f.sum) + (88456386557/17300000000000000000000000 : ℝ)*base65 + (1618595995129462103/43250000000000000000000000000000 : ℝ)*base67 + (258608893282962103/43250000000000000000000000000000 : ℝ)*base69 + (2590469263230962103/43250000000000000000000000000000 : ℝ)*base71 + (321135376249/173000000000000000000000000 : ℝ)*base73 + (1471373834570037897/43250000000000000000000000000000 : ℝ)*base76 + (550550964115962103/43250000000000000000000000000000 : ℝ)*base77 + (177910347856462103/43250000000000000000000000000000 : ℝ)*base79 + (29614793607/86500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (75646919/10000000000000000000000 : ℝ)*base90 + (75646919/10000000000000000000000 : ℝ)*base92 + (75646919/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1401_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157058059/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7371/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5641/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5641/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14741/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1401_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1401_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157058059/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14747/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11277/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5641/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14741/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1401_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1401_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1401_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157058059/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14747/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11277/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5641/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14741/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1401_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
