-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1483_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:14:03.562328+00:00
-- url     : https://prove2.me/submissions/55beb254-2ef4-405e-8040-e1751117c583

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
theorem support_rectangle_w1483_s3_0 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1911024143/10000000000 : ℝ)*x 0 + (5441585103/10000000000 : ℝ)*x 1 + (2605970749/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1911024143/10000000000 : ℝ)^4463 ≤ (2334991387911/20000000000000 : ℝ)^3439 := by
    have hnat : (1911024143 : ℕ)^4463*20000000000000^3439 ≤ 2334991387911^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1911024143 10000000000 2334991387911 20000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5441585103/10000000000 : ℝ)^4463 ≤ (22698898063853/50000000000000 : ℝ)^3439 := by
    have hnat : (5441585103 : ℕ)^4463*50000000000000^3439 ≤ 22698898063853^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441585103 10000000000 22698898063853 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2605970749/5000000000 : ℝ)^4463 ≤ (42927246922271/100000000000000 : ℝ)^3439 := by
    have hnat : (2605970749 : ℕ)^4463*100000000000000^3439 ≤ 42927246922271^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2605970749 5000000000 42927246922271 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1911024143/10000000000 : ℝ), (5441585103/10000000000 : ℝ), (2605970749/5000000000 : ℝ)] ![(2334991387911/20000000000000 : ℝ), (22698898063853/50000000000000 : ℝ), (42927246922271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1911024143/10000000000 : ℝ)|^4463 ≤ (2334991387911/20000000000000 : ℝ)^3439
        have hw : |(-1911024143/10000000000 : ℝ)|=(1911024143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5441585103/10000000000 : ℝ)|^4463 ≤ (22698898063853/50000000000000 : ℝ)^3439
        have hw : |(5441585103/10000000000 : ℝ)|=(5441585103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2605970749/5000000000 : ℝ)|^4463 ≤ (42927246922271/100000000000000 : ℝ)^3439
        have hw : |(2605970749/5000000000 : ℝ)|=(2605970749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s3_1 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070867197/2000000000 : ℝ)*x 0 + (-1014409559/5000000000 : ℝ)*x 1 + (521194167/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070867197/2000000000 : ℝ)^4463 ≤ (1778216891361/4000000000000 : ℝ)^3439 := by
    have hnat : (1070867197 : ℕ)^4463*4000000000000^3439 ≤ 1778216891361^3439*2000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070867197 2000000000 1778216891361 4000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1014409559/5000000000 : ℝ)^4463 ≤ (12617328936951/100000000000000 : ℝ)^3439 := by
    have hnat : (1014409559 : ℕ)^4463*100000000000000^3439 ≤ 12617328936951^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1014409559 5000000000 12617328936951 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521194167/1000000000 : ℝ)^4463 ≤ (42927248760741/100000000000000 : ℝ)^3439 := by
    have hnat : (521194167 : ℕ)^4463*100000000000000^3439 ≤ 42927248760741^3439*1000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521194167 1000000000 42927248760741 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070867197/2000000000 : ℝ), (-1014409559/5000000000 : ℝ), (521194167/1000000000 : ℝ)] ![(1778216891361/4000000000000 : ℝ), (12617328936951/100000000000000 : ℝ), (42927248760741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070867197/2000000000 : ℝ)|^4463 ≤ (1778216891361/4000000000000 : ℝ)^3439
        have hw : |(1070867197/2000000000 : ℝ)|=(1070867197/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1014409559/5000000000 : ℝ)|^4463 ≤ (12617328936951/100000000000000 : ℝ)^3439
        have hw : |(-1014409559/5000000000 : ℝ)|=(1014409559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521194167/1000000000 : ℝ)|^4463 ≤ (42927248760741/100000000000000 : ℝ)^3439
        have hw : |(521194167/1000000000 : ℝ)|=(521194167/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s3_2 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354335967/10000000000 : ℝ)*x 0 + (2605970743/5000000000 : ℝ)*x 1 + (-2028819387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354335967/10000000000 : ℝ)^4463 ≤ (11113855522519/25000000000000 : ℝ)^3439 := by
    have hnat : (5354335967 : ℕ)^4463*25000000000000^3439 ≤ 11113855522519^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354335967 10000000000 11113855522519 25000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2605970743/5000000000 : ℝ)^4463 ≤ (21463623397003/50000000000000 : ℝ)^3439 := by
    have hnat : (2605970743 : ℕ)^4463*50000000000000^3439 ≤ 21463623397003^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2605970743 5000000000 21463623397003 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2028819387/10000000000 : ℝ)^4463 ≤ (1577166388501/12500000000000 : ℝ)^3439 := by
    have hnat : (2028819387 : ℕ)^4463*12500000000000^3439 ≤ 1577166388501^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2028819387 10000000000 1577166388501 12500000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354335967/10000000000 : ℝ), (2605970743/5000000000 : ℝ), (-2028819387/10000000000 : ℝ)] ![(11113855522519/25000000000000 : ℝ), (21463623397003/50000000000000 : ℝ), (1577166388501/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354335967/10000000000 : ℝ)|^4463 ≤ (11113855522519/25000000000000 : ℝ)^3439
        have hw : |(5354335967/10000000000 : ℝ)|=(5354335967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2605970743/5000000000 : ℝ)|^4463 ≤ (21463623397003/50000000000000 : ℝ)^3439
        have hw : |(2605970743/5000000000 : ℝ)|=(2605970743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2028819387/10000000000 : ℝ)|^4463 ≤ (1577166388501/12500000000000 : ℝ)^3439
        have hw : |(-2028819387/10000000000 : ℝ)|=(2028819387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s3_3 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (856607011/2000000000 : ℝ)*x 0 + (2017291969/5000000000 : ℝ)*x 1 + (4544696163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (856607011/2000000000 : ℝ)^4463 ≤ (6654748236981/20000000000000 : ℝ)^3439 := by
    have hnat : (856607011 : ℕ)^4463*20000000000000^3439 ≤ 6654748236981^3439*2000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      856607011 2000000000 6654748236981 20000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2017291969/5000000000 : ℝ)^4463 ≤ (6158160491253/20000000000000 : ℝ)^3439 := by
    have hnat : (2017291969 : ℕ)^4463*20000000000000^3439 ≤ 6158160491253^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017291969 5000000000 6158160491253 20000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4544696163/10000000000 : ℝ)^4463 ≤ (17967728168167/50000000000000 : ℝ)^3439 := by
    have hnat : (4544696163 : ℕ)^4463*50000000000000^3439 ≤ 17967728168167^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4544696163 10000000000 17967728168167 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(856607011/2000000000 : ℝ), (2017291969/5000000000 : ℝ), (4544696163/10000000000 : ℝ)] ![(6654748236981/20000000000000 : ℝ), (6158160491253/20000000000000 : ℝ), (17967728168167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(856607011/2000000000 : ℝ)|^4463 ≤ (6654748236981/20000000000000 : ℝ)^3439
        have hw : |(856607011/2000000000 : ℝ)|=(856607011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2017291969/5000000000 : ℝ)|^4463 ≤ (6158160491253/20000000000000 : ℝ)^3439
        have hw : |(2017291969/5000000000 : ℝ)|=(2017291969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4544696163/10000000000 : ℝ)|^4463 ≤ (17967728168167/50000000000000 : ℝ)^3439
        have hw : |(4544696163/10000000000 : ℝ)|=(4544696163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s3_4 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1911057921/10000000000 : ℝ)*x 0 + (2606581333/5000000000 : ℝ)*x 1 + (5440354693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1911057921/10000000000 : ℝ)^4463 ≤ (11675224744689/100000000000000 : ℝ)^3439 := by
    have hnat : (1911057921 : ℕ)^4463*100000000000000^3439 ≤ 11675224744689^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1911057921 10000000000 11675224744689 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2606581333/5000000000 : ℝ)^4463 ≤ (10735075043993/25000000000000 : ℝ)^3439 := by
    have hnat : (2606581333 : ℕ)^4463*25000000000000^3439 ≤ 10735075043993^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606581333 5000000000 10735075043993 25000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5440354693/10000000000 : ℝ)^4463 ≤ (45384475052299/100000000000000 : ℝ)^3439 := by
    have hnat : (5440354693 : ℕ)^4463*100000000000000^3439 ≤ 45384475052299^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440354693 10000000000 45384475052299 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1911057921/10000000000 : ℝ), (2606581333/5000000000 : ℝ), (5440354693/10000000000 : ℝ)] ![(11675224744689/100000000000000 : ℝ), (10735075043993/25000000000000 : ℝ), (45384475052299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1911057921/10000000000 : ℝ)|^4463 ≤ (11675224744689/100000000000000 : ℝ)^3439
        have hw : |(-1911057921/10000000000 : ℝ)|=(1911057921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2606581333/5000000000 : ℝ)|^4463 ≤ (10735075043993/25000000000000 : ℝ)^3439
        have hw : |(2606581333/5000000000 : ℝ)|=(2606581333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5440354693/10000000000 : ℝ)|^4463 ≤ (45384475052299/100000000000000 : ℝ)^3439
        have hw : |(5440354693/10000000000 : ℝ)|=(5440354693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s3_5 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323581981/2500000000 : ℝ)*x 0 + (-225050793/1250000000 : ℝ)*x 1 + (5440354823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323581981/2500000000 : ℝ)^4463 ≤ (43809922263629/100000000000000 : ℝ)^3439 := by
    have hnat : (1323581981 : ℕ)^4463*100000000000000^3439 ≤ 43809922263629^3439*2500000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323581981 2500000000 43809922263629 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225050793/1250000000 : ℝ)^4463 ≤ (10805601258079/100000000000000 : ℝ)^3439 := by
    have hnat : (225050793 : ℕ)^4463*100000000000000^3439 ≤ 10805601258079^3439*1250000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225050793 1250000000 10805601258079 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5440354823/10000000000 : ℝ)^4463 ≤ (45384476459701/100000000000000 : ℝ)^3439 := by
    have hnat : (5440354823 : ℕ)^4463*100000000000000^3439 ≤ 45384476459701^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440354823 10000000000 45384476459701 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323581981/2500000000 : ℝ), (-225050793/1250000000 : ℝ), (5440354823/10000000000 : ℝ)] ![(43809922263629/100000000000000 : ℝ), (10805601258079/100000000000000 : ℝ), (45384476459701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323581981/2500000000 : ℝ)|^4463 ≤ (43809922263629/100000000000000 : ℝ)^3439
        have hw : |(1323581981/2500000000 : ℝ)|=(1323581981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-225050793/1250000000 : ℝ)|^4463 ≤ (10805601258079/100000000000000 : ℝ)^3439
        have hw : |(-225050793/1250000000 : ℝ)|=(225050793/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5440354823/10000000000 : ℝ)|^4463 ≤ (45384476459701/100000000000000 : ℝ)^3439
        have hw : |(5440354823/10000000000 : ℝ)|=(5440354823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s3_6 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294328373/10000000000 : ℝ)*x 0 + (5440354361/10000000000 : ℝ)*x 1 + (-900203183/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294328373/10000000000 : ℝ)^4463 ≤ (43809927085357/100000000000000 : ℝ)^3439 := by
    have hnat : (5294328373 : ℕ)^4463*100000000000000^3439 ≤ 43809927085357^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294328373 10000000000 43809927085357 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5440354361/10000000000 : ℝ)^4463 ≤ (45384471458011/100000000000000 : ℝ)^3439 := by
    have hnat : (5440354361 : ℕ)^4463*100000000000000^3439 ≤ 45384471458011^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440354361 10000000000 45384471458011 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (900203183/5000000000 : ℝ)^4463 ≤ (5402800714717/50000000000000 : ℝ)^3439 := by
    have hnat : (900203183 : ℕ)^4463*50000000000000^3439 ≤ 5402800714717^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900203183 5000000000 5402800714717 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294328373/10000000000 : ℝ), (5440354361/10000000000 : ℝ), (-900203183/5000000000 : ℝ)] ![(43809927085357/100000000000000 : ℝ), (45384471458011/100000000000000 : ℝ), (5402800714717/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294328373/10000000000 : ℝ)|^4463 ≤ (43809927085357/100000000000000 : ℝ)^3439
        have hw : |(5294328373/10000000000 : ℝ)|=(5294328373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5440354361/10000000000 : ℝ)|^4463 ≤ (45384471458011/100000000000000 : ℝ)^3439
        have hw : |(5440354361/10000000000 : ℝ)|=(5440354361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-900203183/5000000000 : ℝ)|^4463 ≤ (5402800714717/50000000000000 : ℝ)^3439
        have hw : |(-900203183/5000000000 : ℝ)|=(900203183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s3_7 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070777541/2500000000 : ℝ)*x 0 + (1135495961/2500000000 : ℝ)*x 1 + (4037317153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070777541/2500000000 : ℝ)^4463 ≤ (16637249216187/50000000000000 : ℝ)^3439 := by
    have hnat : (1070777541 : ℕ)^4463*50000000000000^3439 ≤ 16637249216187^3439*2500000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070777541 2500000000 16637249216187 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1135495961/2500000000 : ℝ)^4463 ≤ (1436305048363/4000000000000 : ℝ)^3439 := by
    have hnat : (1135495961 : ℕ)^4463*4000000000000^3439 ≤ 1436305048363^3439*2500000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135495961 2500000000 1436305048363 4000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4037317153/10000000000 : ℝ)^4463 ≤ (30817875342101/100000000000000 : ℝ)^3439 := by
    have hnat : (4037317153 : ℕ)^4463*100000000000000^3439 ≤ 30817875342101^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4037317153 10000000000 30817875342101 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070777541/2500000000 : ℝ), (1135495961/2500000000 : ℝ), (4037317153/10000000000 : ℝ)] ![(16637249216187/50000000000000 : ℝ), (1436305048363/4000000000000 : ℝ), (30817875342101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070777541/2500000000 : ℝ)|^4463 ≤ (16637249216187/50000000000000 : ℝ)^3439
        have hw : |(1070777541/2500000000 : ℝ)|=(1070777541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1135495961/2500000000 : ℝ)|^4463 ≤ (1436305048363/4000000000000 : ℝ)^3439
        have hw : |(1135495961/2500000000 : ℝ)|=(1135495961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4037317153/10000000000 : ℝ)|^4463 ≤ (30817875342101/100000000000000 : ℝ)^3439
        have hw : |(4037317153/10000000000 : ℝ)|=(4037317153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1483_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161066273/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16117/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1021/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (10711/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15571/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16117/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1021/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16117/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1021/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16117/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1021/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16117/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1021/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16117/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1021/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16117/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1021/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1021/10000 : ℝ) ^ (4461/1024 : ℝ) ≤ (4818089235846733/100000000000000000000 : ℝ) := by
    have hpowers : (1021/10000 : ℝ)^4461 ≤ (4818089235846733/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1021 : ℕ)^4461*100000000000000000000^1024 ≤ 4818089235846733^1024*10000^4461 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1021 10000 4818089235846733 100000000000000000000 4461 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1021/10000 : ℝ)) (X := (4818089235846733/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16117/100000 : ℝ) ^ (4461/1024 : ℝ) ≤ (35202782689806521/100000000000000000000 : ℝ) := by
    have hpowers : (16117/100000 : ℝ)^4461 ≤ (35202782689806521/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16117 : ℕ)^4461*100000000000000000000^1024 ≤ 35202782689806521^1024*100000^4461 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16117 100000 35202782689806521 100000000000000000000 4461 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16117/100000 : ℝ)) (X := (35202782689806521/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004818089235846733/50000000000000000000 : ℝ) ≤ (10000221185395299/10000000000000000 : ℝ) ^ (4461/1024 : ℝ) := by
    have hpowers : (50004818089235846733/50000000000000000000 : ℝ)^1024 ≤ (10000221185395299/10000000000000000 : ℝ)^4461 := by
      have hnat : (50004818089235846733 : ℕ)^1024*10000000000000000^4461 ≤ 10000221185395299^4461*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004818089235846733 50000000000000000000 10000221185395299 10000000000000000 1024 4461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000221185395299/10000000000000000 : ℝ)) (X := (50004818089235846733/50000000000000000000 : ℝ)) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020010435962826627/50000000000000000000 : ℝ) ≤ (10000918517287323/10000000000000000 : ℝ) ^ (4461/1024 : ℝ) := by
    have hpowers : (50020010435962826627/50000000000000000000 : ℝ)^1024 ≤ (10000918517287323/10000000000000000 : ℝ)^4461 := by
      have hnat : (50020010435962826627 : ℕ)^1024*10000000000000000^4461 ≤ 10000918517287323^4461*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020010435962826627 50000000000000000000 10000918517287323 10000000000000000 1024 4461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000918517287323/10000000000000000 : ℝ)) (X := (50020010435962826627/50000000000000000000 : ℝ)) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035202782689806521/50000000000000000000 : ℝ) ≤ (10001615849179347/10000000000000000 : ℝ) ^ (4461/1024 : ℝ) := by
    have hpowers : (50035202782689806521/50000000000000000000 : ℝ)^1024 ≤ (10001615849179347/10000000000000000 : ℝ)^4461 := by
      have hnat : (50035202782689806521 : ℕ)^1024*10000000000000000^4461 ≤ 10001615849179347^4461*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035202782689806521 50000000000000000000 10001615849179347 10000000000000000 1024 4461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001615849179347/10000000000000000 : ℝ)) (X := (50035202782689806521/50000000000000000000 : ℝ)) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4818089235846733/100000000000000000000 : ℝ) ≤ ((19685689008298300371/19690000000000000000 : ℝ)+2*(29055495501/24612500000000 : ℝ)*(1021/10000 : ℝ))^(4461/1024 : ℝ) := by
    rw [show (19685689008298300371/19690000000000000000 : ℝ)+2*(29055495501/24612500000000 : ℝ)*(1021/10000 : ℝ)=(10000221185395299/10000000000000000 : ℝ) by norm_num, show 1+2*(4818089235846733/100000000000000000000 : ℝ)=(50004818089235846733/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35202782689806521/100000000000000000000 : ℝ)+(4818089235846733/100000000000000000000 : ℝ) ≤ ((19685689008298300371/19690000000000000000 : ℝ)+(29055495501/24612500000000 : ℝ)*((16117/100000 : ℝ)+(1021/10000 : ℝ)))^(4461/1024 : ℝ) := by
    rw [show (19685689008298300371/19690000000000000000 : ℝ)+(29055495501/24612500000000 : ℝ)*((16117/100000 : ℝ)+(1021/10000 : ℝ))=(10000918517287323/10000000000000000 : ℝ) by norm_num, show 1+(35202782689806521/100000000000000000000 : ℝ)+(4818089235846733/100000000000000000000 : ℝ)=(50020010435962826627/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35202782689806521/100000000000000000000 : ℝ) ≤ ((19685689008298300371/19690000000000000000 : ℝ)+2*(29055495501/24612500000000 : ℝ)*(16117/100000 : ℝ))^(4461/1024 : ℝ) := by
    rw [show (19685689008298300371/19690000000000000000 : ℝ)+2*(29055495501/24612500000000 : ℝ)*(16117/100000 : ℝ)=(10001615849179347/10000000000000000 : ℝ) by norm_num, show 1+2*(35202782689806521/100000000000000000000 : ℝ)=(50035202782689806521/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19685689008298300371/19690000000000000000 : ℝ)*(X 1 0+X 2 0)+(29055495501/24612500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4461/1024 : ℝ)) (lo := (1021/10000 : ℝ)) (hi := (16117/100000 : ℝ)) (c := (19685689008298300371/19690000000000000000 : ℝ)) (alpha := (29055495501/24612500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19685689008298300371/19690000000000000000 : ℝ)*(X 0 1+X 2 1)+(29055495501/24612500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4461/1024 : ℝ)) (lo := (1021/10000 : ℝ)) (hi := (16117/100000 : ℝ)) (c := (19685689008298300371/19690000000000000000 : ℝ)) (alpha := (29055495501/24612500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19685689008298300371/19690000000000000000 : ℝ)*(X 0 2+X 1 2)+(29055495501/24612500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4461/1024 : ℝ)) (lo := (1021/10000 : ℝ)) (hi := (16117/100000 : ℝ)) (c := (19685689008298300371/19690000000000000000 : ℝ)) (alpha := (29055495501/24612500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1911024143/10000000000 : ℝ)*X 0 0+(5441585103/10000000000 : ℝ)*X 0 1+(2605970749/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070867197/2000000000 : ℝ)*X 1 0+(-1014409559/5000000000 : ℝ)*X 1 1+(521194167/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354335967/10000000000 : ℝ)*X 2 0+(2605970743/5000000000 : ℝ)*X 2 1+(-2028819387/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((856607011/2000000000 : ℝ)*X 0 0+(2017291969/5000000000 : ℝ)*X 0 1+(4544696163/10000000000 : ℝ)*X 0 2+(856607011/2000000000 : ℝ)*X 1 0+(2017291969/5000000000 : ℝ)*X 1 1+(4544696163/10000000000 : ℝ)*X 1 2+(856607011/2000000000 : ℝ)*X 2 0+(2017291969/5000000000 : ℝ)*X 2 1+(4544696163/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1911057921/10000000000 : ℝ)*X 0 0+(2606581333/5000000000 : ℝ)*X 0 1+(5440354693/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323581981/2500000000 : ℝ)*X 1 0+(-225050793/1250000000 : ℝ)*X 1 1+(5440354823/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294328373/10000000000 : ℝ)*X 2 0+(5440354361/10000000000 : ℝ)*X 2 1+(-900203183/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1070777541/2500000000 : ℝ)*X 0 0+(1135495961/2500000000 : ℝ)*X 0 1+(4037317153/10000000000 : ℝ)*X 0 2+(1070777541/2500000000 : ℝ)*X 1 0+(1135495961/2500000000 : ℝ)*X 1 1+(4037317153/10000000000 : ℝ)*X 1 2+(1070777541/2500000000 : ℝ)*X 2 0+(1135495961/2500000000 : ℝ)*X 2 1+(4037317153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (352224699318132197089250859/44750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (842882743/50000000000000 : ℝ)*(base19) + (96680047/6250000000000 : ℝ)*(base23) + (36497889/50000000000000 : ℝ)*(lower2) + (169967951/50000000000000 : ℝ)*(upper3) + (1294111/20000000000000 : ℝ)*(lower4) + (1578750997791473/50000000000000 : ℝ)*(major0) + (1578750997791473/50000000000000 : ℝ)*(major1) + (1578750997791473/50000000000000 : ℝ)*(major2) + (2177302793423499/50000000000000 : ℝ)*(sp0) + (108865690879437/2500000000000 : ℝ)*(sp1) + (2177313887031107/50000000000000 : ℝ)*(sp2) + (490090424617847/25000000000000 : ℝ)*(sp3) + (741690499/3125000000000 : ℝ)*(sp4) + (2541877353/20000000000000 : ℝ)*(sp7) + (1960374407858153/100000000000000 : ℝ)*(f.failure) + (2177314660471483/50000000000000 : ℝ)*(f.sum) + (4286794175639/447500000000000000000000000 : ℝ)*base65 + (389541807064733047/89500000000000000000000000000000 : ℝ)*base68 + (644480143339233047/89500000000000000000000000000000 : ℝ)*base70 + (560275912432266953/89500000000000000000000000000000 : ℝ)*base71 + (531819981773/223750000000000000000000000 : ℝ)*base74 + (1573802567433233047/89500000000000000000000000000000 : ℝ)*base76 + (641700046581266953/89500000000000000000000000000000 : ℝ)*base77 + (317566669783733047/89500000000000000000000000000000 : ℝ)*base80 + (2789126615857/895000000000000000000000000 : ℝ)*base82 + (16373769/10000000000000000000000 : ℝ)*base89 + (16373769/10000000000000000000000 : ℝ)*base91 + (16373769/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2935243575084013061290193499/492250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (161730289/25000000000000 : ℝ)*(base19) + (1178613689/100000000000000 : ℝ)*(base23) + (5272207/25000000000000 : ℝ)*(upper3) + (82884541/100000000000000 : ℝ)*(lower4) + (75629461/50000000000000 : ℝ)*(upper5) + (1595768046331677/50000000000000 : ℝ)*(major0) + (1595768046331677/50000000000000 : ℝ)*(major1) + (1595768046331677/50000000000000 : ℝ)*(major2) + (14495865549/100000000000000 : ℝ)*(sp1) + (1465939293/10000000000000 : ℝ)*(sp2) + (2200783542995579/50000000000000 : ℝ)*(sp4) + (2200775971602227/50000000000000 : ℝ)*(sp5) + (220077562399227/5000000000000 : ℝ)*(sp6) + (9907524502859/500000000000 : ℝ)*(sp7) + (9907524502859/500000000000 : ℝ)*(f.failure) + (2200783542995579/50000000000000 : ℝ)*(f.sum) + (18129151895729/4922500000000000000000000000 : ℝ)*base66 + (7278427150213752167/984500000000000000000000000000000 : ℝ)*base67 + (11179623127936752167/984500000000000000000000000000000 : ℝ)*base69 + (178682724225252167/984500000000000000000000000000000 : ℝ)*base71 + (20450131807671/4922500000000000000000000000 : ℝ)*base73 + (8473658938404247833/984500000000000000000000000000000 : ℝ)*base76 + (6985503448494752167/984500000000000000000000000000000 : ℝ)*base77 + (2172739073560247833/984500000000000000000000000000000 : ℝ)*base80 + (12548571194791/4922500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (25493/50000000000000000000 : ℝ)*base90 + (25493/50000000000000000000 : ℝ)*base92 + (25493/50000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1483_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161066273/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16117/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1021/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10711/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15571/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1483_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1483_s4_0 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1911632881/10000000000 : ℝ)*x 0 + (5437638483/10000000000 : ℝ)*x 1 + (1303871693/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1911632881/10000000000 : ℝ)^4463 ≤ (1459972933447/12500000000000 : ℝ)^3439 := by
    have hnat : (1911632881 : ℕ)^4463*12500000000000^3439 ≤ 1459972933447^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1911632881 10000000000 1459972933447 12500000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437638483/10000000000 : ℝ)^4463 ≤ (9071014217837/20000000000000 : ℝ)^3439 := by
    have hnat : (5437638483 : ℕ)^4463*20000000000000^3439 ≤ 9071014217837^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437638483 10000000000 9071014217837 20000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303871693/2500000000 : ℝ)^4463 ≤ (859302908397/2000000000000 : ℝ)^3439 := by
    have hnat : (1303871693 : ℕ)^4463*2000000000000^3439 ≤ 859302908397^3439*2500000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303871693 2500000000 859302908397 2000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1911632881/10000000000 : ℝ), (5437638483/10000000000 : ℝ), (1303871693/2500000000 : ℝ)] ![(1459972933447/12500000000000 : ℝ), (9071014217837/20000000000000 : ℝ), (859302908397/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1911632881/10000000000 : ℝ)|^4463 ≤ (1459972933447/12500000000000 : ℝ)^3439
        have hw : |(-1911632881/10000000000 : ℝ)|=(1911632881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437638483/10000000000 : ℝ)|^4463 ≤ (9071014217837/20000000000000 : ℝ)^3439
        have hw : |(5437638483/10000000000 : ℝ)|=(5437638483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1303871693/2500000000 : ℝ)|^4463 ≤ (859302908397/2000000000000 : ℝ)^3439
        have hw : |(1303871693/2500000000 : ℝ)|=(1303871693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s4_1 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353310877/10000000000 : ℝ)*x 0 + (-2025491893/10000000000 : ℝ)*x 1 + (651935793/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353310877/10000000000 : ℝ)^4463 ≤ (22222188573929/50000000000000 : ℝ)^3439 := by
    have hnat : (5353310877 : ℕ)^4463*50000000000000^3439 ≤ 22222188573929^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353310877 10000000000 22222188573929 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2025491893/10000000000 : ℝ)^4463 ≤ (3147620497777/25000000000000 : ℝ)^3439 := by
    have hnat : (2025491893 : ℕ)^4463*25000000000000^3439 ≤ 3147620497777^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025491893 10000000000 3147620497777 25000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (651935793/1250000000 : ℝ)^4463 ≤ (21482570422063/50000000000000 : ℝ)^3439 := by
    have hnat : (651935793 : ℕ)^4463*50000000000000^3439 ≤ 21482570422063^3439*1250000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651935793 1250000000 21482570422063 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353310877/10000000000 : ℝ), (-2025491893/10000000000 : ℝ), (651935793/1250000000 : ℝ)] ![(22222188573929/50000000000000 : ℝ), (3147620497777/25000000000000 : ℝ), (21482570422063/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353310877/10000000000 : ℝ)|^4463 ≤ (22222188573929/50000000000000 : ℝ)^3439
        have hw : |(5353310877/10000000000 : ℝ)|=(5353310877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2025491893/10000000000 : ℝ)|^4463 ≤ (3147620497777/25000000000000 : ℝ)^3439
        have hw : |(-2025491893/10000000000 : ℝ)|=(2025491893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(651935793/1250000000 : ℝ)|^4463 ≤ (21482570422063/50000000000000 : ℝ)^3439
        have hw : |(651935793/1250000000 : ℝ)|=(651935793/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s4_2 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669163839/1250000000 : ℝ)*x 0 + (4074599/7812500 : ℝ)*x 1 + (-405098323/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669163839/1250000000 : ℝ)^4463 ≤ (22222187685049/50000000000000 : ℝ)^3439 := by
    have hnat : (669163839 : ℕ)^4463*50000000000000^3439 ≤ 22222187685049^3439*1250000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669163839 1250000000 22222187685049 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4074599/7812500 : ℝ)^4463 ≤ (42965144863921/100000000000000 : ℝ)^3439 := by
    have hnat : (4074599 : ℕ)^4463*100000000000000^3439 ≤ 42965144863921^3439*7812500^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4074599 7812500 42965144863921 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (405098323/2000000000 : ℝ)^4463 ≤ (1259047974851/10000000000000 : ℝ)^3439 := by
    have hnat : (405098323 : ℕ)^4463*10000000000000^3439 ≤ 1259047974851^3439*2000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      405098323 2000000000 1259047974851 10000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669163839/1250000000 : ℝ), (4074599/7812500 : ℝ), (-405098323/2000000000 : ℝ)] ![(22222187685049/50000000000000 : ℝ), (42965144863921/100000000000000 : ℝ), (1259047974851/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669163839/1250000000 : ℝ)|^4463 ≤ (22222187685049/50000000000000 : ℝ)^3439
        have hw : |(669163839/1250000000 : ℝ)|=(669163839/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4074599/7812500 : ℝ)|^4463 ≤ (42965144863921/100000000000000 : ℝ)^3439
        have hw : |(4074599/7812500 : ℝ)|=(4074599/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-405098323/2000000000 : ℝ)|^4463 ≤ (1259047974851/10000000000000 : ℝ)^3439
        have hw : |(-405098323/2000000000 : ℝ)|=(405098323/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s4_3 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4283413357/10000000000 : ℝ)*x 0 + (1010715119/2500000000 : ℝ)*x 1 + (2268165739/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4283413357/10000000000 : ℝ)^4463 ≤ (16638777629231/50000000000000 : ℝ)^3439 := by
    have hnat : (4283413357 : ℕ)^4463*50000000000000^3439 ≤ 16638777629231^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4283413357 10000000000 16638777629231 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1010715119/2500000000 : ℝ)^4463 ≤ (15436399753499/50000000000000 : ℝ)^3439 := by
    have hnat : (1010715119 : ℕ)^4463*50000000000000^3439 ≤ 15436399753499^3439*2500000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010715119 2500000000 15436399753499 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2268165739/5000000000 : ℝ)^4463 ≤ (8962411305617/25000000000000 : ℝ)^3439 := by
    have hnat : (2268165739 : ℕ)^4463*25000000000000^3439 ≤ 8962411305617^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2268165739 5000000000 8962411305617 25000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4283413357/10000000000 : ℝ), (1010715119/2500000000 : ℝ), (2268165739/5000000000 : ℝ)] ![(16638777629231/50000000000000 : ℝ), (15436399753499/50000000000000 : ℝ), (8962411305617/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4283413357/10000000000 : ℝ)|^4463 ≤ (16638777629231/50000000000000 : ℝ)^3439
        have hw : |(4283413357/10000000000 : ℝ)|=(4283413357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1010715119/2500000000 : ℝ)|^4463 ≤ (15436399753499/50000000000000 : ℝ)^3439
        have hw : |(1010715119/2500000000 : ℝ)|=(1010715119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2268165739/5000000000 : ℝ)|^4463 ≤ (8962411305617/25000000000000 : ℝ)^3439
        have hw : |(2268165739/5000000000 : ℝ)|=(2268165739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s4_4 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-38233277/200000000 : ℝ)*x 0 + (65207871/125000000 : ℝ)*x 1 + (217459477/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (38233277/200000000 : ℝ)^4463 ≤ (11680029025097/100000000000000 : ℝ)^3439 := by
    have hnat : (38233277 : ℕ)^4463*100000000000000^3439 ≤ 11680029025097^3439*200000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38233277 200000000 11680029025097 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65207871/125000000 : ℝ)^4463 ≤ (2686085286659/6250000000000 : ℝ)^3439 := by
    have hnat : (65207871 : ℕ)^4463*6250000000000^3439 ≤ 2686085286659^3439*125000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65207871 125000000 2686085286659 6250000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217459477/400000000 : ℝ)^4463 ≤ (11335651593529/25000000000000 : ℝ)^3439 := by
    have hnat : (217459477 : ℕ)^4463*25000000000000^3439 ≤ 11335651593529^3439*400000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217459477 400000000 11335651593529 25000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-38233277/200000000 : ℝ), (65207871/125000000 : ℝ), (217459477/400000000 : ℝ)] ![(11680029025097/100000000000000 : ℝ), (2686085286659/6250000000000 : ℝ), (11335651593529/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-38233277/200000000 : ℝ)|^4463 ≤ (11680029025097/100000000000000 : ℝ)^3439
        have hw : |(-38233277/200000000 : ℝ)|=(38233277/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(65207871/125000000 : ℝ)|^4463 ≤ (2686085286659/6250000000000 : ℝ)^3439
        have hw : |(65207871/125000000 : ℝ)|=(65207871/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(217459477/400000000 : ℝ)|^4463 ≤ (11335651593529/25000000000000 : ℝ)^3439
        have hw : |(217459477/400000000 : ℝ)|=(217459477/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s4_5 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647631389/5000000000 : ℝ)*x 0 + (-45112291/250000000 : ℝ)*x 1 + (679560867/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647631389/5000000000 : ℝ)^4463 ≤ (43819961751589/100000000000000 : ℝ)^3439 := by
    have hnat : (2647631389 : ℕ)^4463*100000000000000^3439 ≤ 43819961751589^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647631389 5000000000 43819961751589 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (45112291/250000000 : ℝ)^4463 ≤ (433497269721/4000000000000 : ℝ)^3439 := by
    have hnat : (45112291 : ℕ)^4463*4000000000000^3439 ≤ 433497269721^3439*250000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45112291 250000000 433497269721 4000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (679560867/1250000000 : ℝ)^4463 ≤ (45342606493179/100000000000000 : ℝ)^3439 := by
    have hnat : (679560867 : ℕ)^4463*100000000000000^3439 ≤ 45342606493179^3439*1250000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679560867 1250000000 45342606493179 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647631389/5000000000 : ℝ), (-45112291/250000000 : ℝ), (679560867/1250000000 : ℝ)] ![(43819961751589/100000000000000 : ℝ), (433497269721/4000000000000 : ℝ), (45342606493179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647631389/5000000000 : ℝ)|^4463 ≤ (43819961751589/100000000000000 : ℝ)^3439
        have hw : |(2647631389/5000000000 : ℝ)|=(2647631389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-45112291/250000000 : ℝ)|^4463 ≤ (433497269721/4000000000000 : ℝ)^3439
        have hw : |(-45112291/250000000 : ℝ)|=(45112291/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(679560867/1250000000 : ℝ)|^4463 ≤ (45342606493179/100000000000000 : ℝ)^3439
        have hw : |(679560867/1250000000 : ℝ)|=(679560867/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s4_6 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647631403/5000000000 : ℝ)*x 0 + (2718243461/5000000000 : ℝ)*x 1 + (-90224581/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647631403/5000000000 : ℝ)^4463 ≤ (43819962052291/100000000000000 : ℝ)^3439 := by
    have hnat : (2647631403 : ℕ)^4463*100000000000000^3439 ≤ 43819962052291^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647631403 5000000000 43819962052291 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718243461/5000000000 : ℝ)^4463 ≤ (11335651585411/25000000000000 : ℝ)^3439 := by
    have hnat : (2718243461 : ℕ)^4463*25000000000000^3439 ≤ 11335651585411^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718243461 5000000000 11335651585411 25000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90224581/500000000 : ℝ)^4463 ≤ (10837431587143/100000000000000 : ℝ)^3439 := by
    have hnat : (90224581 : ℕ)^4463*100000000000000^3439 ≤ 10837431587143^3439*500000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90224581 500000000 10837431587143 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647631403/5000000000 : ℝ), (2718243461/5000000000 : ℝ), (-90224581/500000000 : ℝ)] ![(43819962052291/100000000000000 : ℝ), (11335651585411/25000000000000 : ℝ), (10837431587143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647631403/5000000000 : ℝ)|^4463 ≤ (43819962052291/100000000000000 : ℝ)^3439
        have hw : |(2647631403/5000000000 : ℝ)|=(2647631403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718243461/5000000000 : ℝ)|^4463 ≤ (11335651585411/25000000000000 : ℝ)^3439
        have hw : |(2718243461/5000000000 : ℝ)|=(2718243461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-90224581/500000000 : ℝ)|^4463 ≤ (10837431587143/100000000000000 : ℝ)^3439
        have hw : |(-90224581/500000000 : ℝ)|=(90224581/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s4_7 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070870547/2500000000 : ℝ)*x 0 + (4533792279/10000000000 : ℝ)*x 1 + (4045417773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070870547/2500000000 : ℝ)^4463 ≤ (8319562307339/25000000000000 : ℝ)^3439 := by
    have hnat : (1070870547 : ℕ)^4463*25000000000000^3439 ≤ 8319562307339^3439*2500000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070870547 2500000000 8319562307339 25000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4533792279/10000000000 : ℝ)^4463 ≤ (7164721112229/20000000000000 : ℝ)^3439 := by
    have hnat : (4533792279 : ℕ)^4463*20000000000000^3439 ≤ 7164721112229^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4533792279 10000000000 7164721112229 20000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4045417773/10000000000 : ℝ)^4463 ≤ (15449072595919/50000000000000 : ℝ)^3439 := by
    have hnat : (4045417773 : ℕ)^4463*50000000000000^3439 ≤ 15449072595919^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4045417773 10000000000 15449072595919 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070870547/2500000000 : ℝ), (4533792279/10000000000 : ℝ), (4045417773/10000000000 : ℝ)] ![(8319562307339/25000000000000 : ℝ), (7164721112229/20000000000000 : ℝ), (15449072595919/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070870547/2500000000 : ℝ)|^4463 ≤ (8319562307339/25000000000000 : ℝ)^3439
        have hw : |(1070870547/2500000000 : ℝ)|=(1070870547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4533792279/10000000000 : ℝ)|^4463 ≤ (7164721112229/20000000000000 : ℝ)^3439
        have hw : |(4533792279/10000000000 : ℝ)|=(4533792279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4045417773/10000000000 : ℝ)|^4463 ≤ (15449072595919/50000000000000 : ℝ)^3439
        have hw : |(4045417773/10000000000 : ℝ)|=(4045417773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1483_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161066273/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15571/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10711/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10787/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15489/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15571/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10711/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15571/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10711/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15571/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10711/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15571/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10711/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15571/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10711/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15571/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10711/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10711/100000 : ℝ) ^ (4461/1024 : ℝ) ≤ (2968093238899079/50000000000000000000 : ℝ) := by
    have hpowers : (10711/100000 : ℝ)^4461 ≤ (2968093238899079/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10711 : ℕ)^4461*50000000000000000000^1024 ≤ 2968093238899079^1024*100000^4461 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10711 100000 2968093238899079 50000000000000000000 4461 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10711/100000 : ℝ)) (X := (2968093238899079/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15571/100000 : ℝ) ^ (4461/1024 : ℝ) ≤ (30295004610652057/100000000000000000000 : ℝ) := by
    have hpowers : (15571/100000 : ℝ)^4461 ≤ (30295004610652057/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15571 : ℕ)^4461*100000000000000000000^1024 ≤ 30295004610652057^1024*100000^4461 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15571 100000 30295004610652057 100000000000000000000 4461 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15571/100000 : ℝ)) (X := (30295004610652057/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002968093238899079/25000000000000000000 : ℝ) ≤ (10000272511856603/10000000000000000 : ℝ) ^ (4461/1024 : ℝ) := by
    have hpowers : (25002968093238899079/25000000000000000000 : ℝ)^1024 ≤ (10000272511856603/10000000000000000 : ℝ)^4461 := by
      have hnat : (25002968093238899079 : ℕ)^1024*10000000000000000^4461 ≤ 10000272511856603^4461*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002968093238899079 25000000000000000000 10000272511856603 10000000000000000 1024 4461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000272511856603/10000000000000000 : ℝ)) (X := (25002968093238899079/25000000000000000000 : ℝ)) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007246238217690043/20000000000000000000 : ℝ) ≤ (1250103944077947/1250000000000000 : ℝ) ^ (4461/1024 : ℝ) := by
    have hpowers : (20007246238217690043/20000000000000000000 : ℝ)^1024 ≤ (1250103944077947/1250000000000000 : ℝ)^4461 := by
      have hnat : (20007246238217690043 : ℕ)^1024*1250000000000000^4461 ≤ 1250103944077947^4461*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007246238217690043 20000000000000000000 1250103944077947 1250000000000000 1024 4461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250103944077947/1250000000000000 : ℝ)) (X := (20007246238217690043/20000000000000000000 : ℝ)) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030295004610652057/50000000000000000000 : ℝ) ≤ (10001390593390549/10000000000000000 : ℝ) ^ (4461/1024 : ℝ) := by
    have hpowers : (50030295004610652057/50000000000000000000 : ℝ)^1024 ≤ (10001390593390549/10000000000000000 : ℝ)^4461 := by
      have hnat : (50030295004610652057 : ℕ)^1024*10000000000000000^4461 ≤ 10001390593390549^4461*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030295004610652057 50000000000000000000 10001390593390549 10000000000000000 1024 4461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001390593390549/10000000000000000 : ℝ)) (X := (50030295004610652057/50000000000000000000 : ℝ)) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2968093238899079/50000000000000000000 : ℝ) ≤ ((24294674318156497487/24300000000000000000 : ℝ)+2*(559040766973/486000000000000 : ℝ)*(10711/100000 : ℝ))^(4461/1024 : ℝ) := by
    rw [show (24294674318156497487/24300000000000000000 : ℝ)+2*(559040766973/486000000000000 : ℝ)*(10711/100000 : ℝ)=(10000272511856603/10000000000000000 : ℝ) by norm_num, show 1+2*(2968093238899079/50000000000000000000 : ℝ)=(25002968093238899079/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30295004610652057/100000000000000000000 : ℝ)+(2968093238899079/50000000000000000000 : ℝ) ≤ ((24294674318156497487/24300000000000000000 : ℝ)+(559040766973/486000000000000 : ℝ)*((15571/100000 : ℝ)+(10711/100000 : ℝ)))^(4461/1024 : ℝ) := by
    rw [show (24294674318156497487/24300000000000000000 : ℝ)+(559040766973/486000000000000 : ℝ)*((15571/100000 : ℝ)+(10711/100000 : ℝ))=(1250103944077947/1250000000000000 : ℝ) by norm_num, show 1+(30295004610652057/100000000000000000000 : ℝ)+(2968093238899079/50000000000000000000 : ℝ)=(20007246238217690043/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30295004610652057/100000000000000000000 : ℝ) ≤ ((24294674318156497487/24300000000000000000 : ℝ)+2*(559040766973/486000000000000 : ℝ)*(15571/100000 : ℝ))^(4461/1024 : ℝ) := by
    rw [show (24294674318156497487/24300000000000000000 : ℝ)+2*(559040766973/486000000000000 : ℝ)*(15571/100000 : ℝ)=(10001390593390549/10000000000000000 : ℝ) by norm_num, show 1+2*(30295004610652057/100000000000000000000 : ℝ)=(50030295004610652057/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (24294674318156497487/24300000000000000000 : ℝ)*(X 1 0+X 2 0)+(559040766973/486000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4461/1024 : ℝ)) (lo := (10711/100000 : ℝ)) (hi := (15571/100000 : ℝ)) (c := (24294674318156497487/24300000000000000000 : ℝ)) (alpha := (559040766973/486000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (24294674318156497487/24300000000000000000 : ℝ)*(X 0 1+X 2 1)+(559040766973/486000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4461/1024 : ℝ)) (lo := (10711/100000 : ℝ)) (hi := (15571/100000 : ℝ)) (c := (24294674318156497487/24300000000000000000 : ℝ)) (alpha := (559040766973/486000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (24294674318156497487/24300000000000000000 : ℝ)*(X 0 2+X 1 2)+(559040766973/486000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4461/1024 : ℝ)) (lo := (10711/100000 : ℝ)) (hi := (15571/100000 : ℝ)) (c := (24294674318156497487/24300000000000000000 : ℝ)) (alpha := (559040766973/486000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1911632881/10000000000 : ℝ)*X 0 0+(5437638483/10000000000 : ℝ)*X 0 1+(1303871693/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353310877/10000000000 : ℝ)*X 1 0+(-2025491893/10000000000 : ℝ)*X 1 1+(651935793/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((669163839/1250000000 : ℝ)*X 2 0+(4074599/7812500 : ℝ)*X 2 1+(-405098323/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4283413357/10000000000 : ℝ)*X 0 0+(1010715119/2500000000 : ℝ)*X 0 1+(2268165739/5000000000 : ℝ)*X 0 2+(4283413357/10000000000 : ℝ)*X 1 0+(1010715119/2500000000 : ℝ)*X 1 1+(2268165739/5000000000 : ℝ)*X 1 2+(4283413357/10000000000 : ℝ)*X 2 0+(1010715119/2500000000 : ℝ)*X 2 1+(2268165739/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-38233277/200000000 : ℝ)*X 0 0+(65207871/125000000 : ℝ)*X 0 1+(217459477/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647631389/5000000000 : ℝ)*X 1 0+(-45112291/250000000 : ℝ)*X 1 1+(679560867/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647631403/5000000000 : ℝ)*X 2 0+(2718243461/5000000000 : ℝ)*X 2 1+(-90224581/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1070870547/2500000000 : ℝ)*X 0 0+(4533792279/10000000000 : ℝ)*X 0 1+(4045417773/10000000000 : ℝ)*X 0 2+(1070870547/2500000000 : ℝ)*X 1 0+(4533792279/10000000000 : ℝ)*X 1 1+(4045417773/10000000000 : ℝ)*X 1 2+(1070870547/2500000000 : ℝ)*X 2 0+(4533792279/10000000000 : ℝ)*X 2 1+(4045417773/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (264167803739753991538754479/33750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (266183767/20000000000000 : ℝ)*(base19) + (4412069/390625000000 : ℝ)*(base23) + (12218541/25000000000000 : ℝ)*(lower2) + (27139431/50000000000000 : ℝ)*(upper5) + (815994023815617/25000000000000 : ℝ)*(major0) + (815994023815617/25000000000000 : ℝ)*(major1) + (815994023815617/25000000000000 : ℝ)*(major2) + (56268112718347/1250000000000 : ℝ)*(sp0) + (562683472791189/12500000000000 : ℝ)*(sp1) + (2250735311227651/50000000000000 : ℝ)*(sp2) + (2026471091433297/100000000000000 : ℝ)*(sp3) + (22734477207/100000000000000 : ℝ)*(sp4) + (131934831/5000000000000 : ℝ)*(sp5) + (9086240193/100000000000000 : ℝ)*(sp7) + (202648017767349/10000000000000 : ℝ)*(f.failure) + (2250735875972483/50000000000000 : ℝ)*(f.sum) + (2714895074093/506250000000000000000000000 : ℝ)*base65 + (1753183296421198507/202500000000000000000000000000000 : ℝ)*base68 + (1232234082848698507/202500000000000000000000000000000 : ℝ)*base70 + (1428209603116198507/202500000000000000000000000000000 : ℝ)*base72 + (1179377059657/506250000000000000000000000 : ℝ)*base74 + (2297191961581198507/202500000000000000000000000000000 : ℝ)*base76 + (745720337716198507/202500000000000000000000000000000 : ℝ)*base78 + (349266510421198507/202500000000000000000000000000000 : ℝ)*base80 + (958106394089/1012500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (4520277/1000000000000000000000 : ℝ)*base89 + (4520277/1000000000000000000000 : ℝ)*base91 + (4520277/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (850177006312921630089760421/101250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (679489111/50000000000000 : ℝ)*(base19) + (1522363363/100000000000000 : ℝ)*(base23) + (173124227/100000000000000 : ℝ)*(upper3) + (60441143/100000000000000 : ℝ)*(lower4) + (85804491/50000000000000 : ℝ)*(upper5) + (824501759387639/25000000000000 : ℝ)*(major0) + (824501759387639/25000000000000 : ℝ)*(major1) + (824501759387639/25000000000000 : ℝ)*(major2) + (20454719233/100000000000000 : ℝ)*(sp1) + (5688224559/25000000000000 : ℝ)*(sp2) + (4548405083512371/100000000000000 : ℝ)*(sp4) + (1137095817453729/25000000000000 : ℝ)*(sp5) + (1137095202062693/25000000000000 : ℝ)*(sp6) + (255951088961883/12500000000000 : ℝ)*(sp7) + (255951088961883/12500000000000 : ℝ)*(f.failure) + (4548405083512371/100000000000000 : ℝ)*(f.sum) + (26036458178597/6075000000000000000000000000 : ℝ)*base65 + (4616663330879713193/607500000000000000000000000000000 : ℝ)*base67 + (5974644827947213193/607500000000000000000000000000000 : ℝ)*base69 + (5791670460742213193/607500000000000000000000000000000 : ℝ)*base71 + (956089963139/3037500000000000000000000000 : ℝ)*base74 + (8392286848499713193/607500000000000000000000000000000 : ℝ)*base75 + (2709764473679713193/607500000000000000000000000000000 : ℝ)*base77 + (4715042838299713193/607500000000000000000000000000000 : ℝ)*base79 + (9633235192847/6075000000000000000000000000 : ℝ)*base81 + (16127941/1250000000000000000000 : ℝ)*base90 + (16127941/1250000000000000000000 : ℝ)*base92 + (16127941/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1483_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161066273/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15571/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10711/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10787/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1483_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1483_s5_0 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-477928587/2500000000 : ℝ)*x 0 + (2718551871/5000000000 : ℝ)*x 1 + (65199597/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (477928587/2500000000 : ℝ)^4463 ≤ (11680429433323/100000000000000 : ℝ)^3439 := by
    have hnat : (477928587 : ℕ)^4463*100000000000000^3439 ≤ 11680429433323^3439*2500000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477928587 2500000000 11680429433323 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718551871/5000000000 : ℝ)^4463 ≤ (9069856567631/20000000000000 : ℝ)^3439 := by
    have hnat : (2718551871 : ℕ)^4463*20000000000000^3439 ≤ 9069856567631^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718551871 5000000000 9069856567631 20000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65199597/125000000 : ℝ)^4463 ≤ (2148514385367/5000000000000 : ℝ)^3439 := by
    have hnat : (65199597 : ℕ)^4463*5000000000000^3439 ≤ 2148514385367^3439*125000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65199597 125000000 2148514385367 5000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-477928587/2500000000 : ℝ), (2718551871/5000000000 : ℝ), (65199597/125000000 : ℝ)] ![(11680429433323/100000000000000 : ℝ), (9069856567631/20000000000000 : ℝ), (2148514385367/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-477928587/2500000000 : ℝ)|^4463 ≤ (11680429433323/100000000000000 : ℝ)^3439
        have hw : |(-477928587/2500000000 : ℝ)|=(477928587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718551871/5000000000 : ℝ)|^4463 ≤ (9069856567631/20000000000000 : ℝ)^3439
        have hw : |(2718551871/5000000000 : ℝ)|=(2718551871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65199597/125000000 : ℝ)|^4463 ≤ (2148514385367/5000000000000 : ℝ)^3439
        have hw : |(65199597/125000000 : ℝ)|=(65199597/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s5_1 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353171479/10000000000 : ℝ)*x 0 + (-2025040143/10000000000 : ℝ)*x 1 + (5215967681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353171479/10000000000 : ℝ)^4463 ≤ (8888575047557/20000000000000 : ℝ)^3439 := by
    have hnat : (5353171479 : ℕ)^4463*20000000000000^3439 ≤ 8888575047557^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353171479 10000000000 8888575047557 20000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2025040143/10000000000 : ℝ)^4463 ≤ (6293418945507/50000000000000 : ℝ)^3439 := by
    have hnat : (2025040143 : ℕ)^4463*50000000000000^3439 ≤ 6293418945507^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025040143 10000000000 6293418945507 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215967681/10000000000 : ℝ)^4463 ≤ (10742571715683/25000000000000 : ℝ)^3439 := by
    have hnat : (5215967681 : ℕ)^4463*25000000000000^3439 ≤ 10742571715683^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215967681 10000000000 10742571715683 25000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353171479/10000000000 : ℝ), (-2025040143/10000000000 : ℝ), (5215967681/10000000000 : ℝ)] ![(8888575047557/20000000000000 : ℝ), (6293418945507/50000000000000 : ℝ), (10742571715683/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353171479/10000000000 : ℝ)|^4463 ≤ (8888575047557/20000000000000 : ℝ)^3439
        have hw : |(5353171479/10000000000 : ℝ)|=(5353171479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2025040143/10000000000 : ℝ)|^4463 ≤ (6293418945507/50000000000000 : ℝ)^3439
        have hw : |(-2025040143/10000000000 : ℝ)|=(2025040143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215967681/10000000000 : ℝ)|^4463 ≤ (10742571715683/25000000000000 : ℝ)^3439
        have hw : |(5215967681/10000000000 : ℝ)|=(5215967681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s5_2 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676585843/5000000000 : ℝ)*x 0 + (1303991879/2500000000 : ℝ)*x 1 + (-1012520043/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676585843/5000000000 : ℝ)^4463 ≤ (2777679841753/6250000000000 : ℝ)^3439 := by
    have hnat : (2676585843 : ℕ)^4463*6250000000000^3439 ≤ 2777679841753^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676585843 5000000000 2777679841753 6250000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1303991879/2500000000 : ℝ)^4463 ≤ (42970285098677/100000000000000 : ℝ)^3439 := by
    have hnat : (1303991879 : ℕ)^4463*100000000000000^3439 ≤ 42970285098677^3439*2500000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303991879 2500000000 42970285098677 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1012520043/5000000000 : ℝ)^4463 ≤ (196669334863/1562500000000 : ℝ)^3439 := by
    have hnat : (1012520043 : ℕ)^4463*1562500000000^3439 ≤ 196669334863^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1012520043 5000000000 196669334863 1562500000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676585843/5000000000 : ℝ), (1303991879/2500000000 : ℝ), (-1012520043/5000000000 : ℝ)] ![(2777679841753/6250000000000 : ℝ), (42970285098677/100000000000000 : ℝ), (196669334863/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676585843/5000000000 : ℝ)|^4463 ≤ (2777679841753/6250000000000 : ℝ)^3439
        have hw : |(2676585843/5000000000 : ℝ)|=(2676585843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1303991879/2500000000 : ℝ)|^4463 ≤ (42970285098677/100000000000000 : ℝ)^3439
        have hw : |(1303991879/2500000000 : ℝ)|=(1303991879/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1012520043/5000000000 : ℝ)|^4463 ≤ (196669334863/1562500000000 : ℝ)^3439
        have hw : |(-1012520043/5000000000 : ℝ)|=(1012520043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s5_3 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2141732337/5000000000 : ℝ)*x 0 + (4043981519/10000000000 : ℝ)*x 1 + (4535197691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2141732337/5000000000 : ℝ)^4463 ≤ (3327807264863/10000000000000 : ℝ)^3439 := by
    have hnat : (2141732337 : ℕ)^4463*10000000000000^3439 ≤ 3327807264863^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141732337 5000000000 3327807264863 10000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4043981519/10000000000 : ℝ)^4463 ≤ (1544195485723/5000000000000 : ℝ)^3439 := by
    have hnat : (4043981519 : ℕ)^4463*5000000000000^3439 ≤ 1544195485723^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4043981519 10000000000 1544195485723 5000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4535197691/10000000000 : ℝ)^4463 ≤ (1791900881097/5000000000000 : ℝ)^3439 := by
    have hnat : (4535197691 : ℕ)^4463*5000000000000^3439 ≤ 1791900881097^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4535197691 10000000000 1791900881097 5000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2141732337/5000000000 : ℝ), (4043981519/10000000000 : ℝ), (4535197691/10000000000 : ℝ)] ![(3327807264863/10000000000000 : ℝ), (1544195485723/5000000000000 : ℝ), (1791900881097/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2141732337/5000000000 : ℝ)|^4463 ≤ (3327807264863/10000000000000 : ℝ)^3439
        have hw : |(2141732337/5000000000 : ℝ)|=(2141732337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4043981519/10000000000 : ℝ)|^4463 ≤ (1544195485723/5000000000000 : ℝ)^3439
        have hw : |(4043981519/10000000000 : ℝ)|=(4043981519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4535197691/10000000000 : ℝ)|^4463 ≤ (1791900881097/5000000000000 : ℝ)^3439
        have hw : |(4535197691/10000000000 : ℝ)|=(4535197691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s5_4 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1911744639/10000000000 : ℝ)*x 0 + (5217100121/10000000000 : ℝ)*x 1 + (1087192607/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1911744639/10000000000 : ℝ)^4463 ≤ (11680669617923/100000000000000 : ℝ)^3439 := by
    have hnat : (1911744639 : ℕ)^4463*100000000000000^3439 ≤ 11680669617923^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1911744639 10000000000 11680669617923 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217100121/10000000000 : ℝ)^4463 ≤ (429823944417/1000000000000 : ℝ)^3439 := by
    have hnat : (5217100121 : ℕ)^4463*1000000000000^3439 ≤ 429823944417^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217100121 10000000000 429823944417 1000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087192607/2000000000 : ℝ)^4463 ≤ (11334233983653/25000000000000 : ℝ)^3439 := by
    have hnat : (1087192607 : ℕ)^4463*25000000000000^3439 ≤ 11334233983653^3439*2000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087192607 2000000000 11334233983653 25000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1911744639/10000000000 : ℝ), (5217100121/10000000000 : ℝ), (1087192607/2000000000 : ℝ)] ![(11680669617923/100000000000000 : ℝ), (429823944417/1000000000000 : ℝ), (11334233983653/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1911744639/10000000000 : ℝ)|^4463 ≤ (11680669617923/100000000000000 : ℝ)^3439
        have hw : |(-1911744639/10000000000 : ℝ)|=(1911744639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217100121/10000000000 : ℝ)|^4463 ≤ (429823944417/1000000000000 : ℝ)^3439
        have hw : |(5217100121/10000000000 : ℝ)|=(5217100121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1087192607/2000000000 : ℝ)|^4463 ≤ (11334233983653/25000000000000 : ℝ)^3439
        have hw : |(1087192607/2000000000 : ℝ)|=(1087192607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s5_5 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295389507/10000000000 : ℝ)*x 0 + (-112815291/625000000 : ℝ)*x 1 + (679495369/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295389507/10000000000 : ℝ)^4463 ≤ (43821322747259/100000000000000 : ℝ)^3439 := by
    have hnat : (5295389507 : ℕ)^4463*100000000000000^3439 ≤ 43821322747259^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295389507 10000000000 43821322747259 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (112815291/625000000 : ℝ)^4463 ≤ (2168348440809/20000000000000 : ℝ)^3439 := by
    have hnat : (112815291 : ℕ)^4463*20000000000000^3439 ≤ 2168348440809^3439*625000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112815291 625000000 2168348440809 20000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (679495369/1250000000 : ℝ)^4463 ≤ (1416779219883/3125000000000 : ℝ)^3439 := by
    have hnat : (679495369 : ℕ)^4463*3125000000000^3439 ≤ 1416779219883^3439*1250000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679495369 1250000000 1416779219883 3125000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295389507/10000000000 : ℝ), (-112815291/625000000 : ℝ), (679495369/1250000000 : ℝ)] ![(43821322747259/100000000000000 : ℝ), (2168348440809/20000000000000 : ℝ), (1416779219883/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295389507/10000000000 : ℝ)|^4463 ≤ (43821322747259/100000000000000 : ℝ)^3439
        have hw : |(5295389507/10000000000 : ℝ)|=(5295389507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-112815291/625000000 : ℝ)|^4463 ≤ (2168348440809/20000000000000 : ℝ)^3439
        have hw : |(-112815291/625000000 : ℝ)|=(112815291/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(679495369/1250000000 : ℝ)|^4463 ≤ (1416779219883/3125000000000 : ℝ)^3439
        have hw : |(679495369/1250000000 : ℝ)|=(679495369/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s5_6 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295389507/10000000000 : ℝ)*x 0 + (2717981501/5000000000 : ℝ)*x 1 + (-1805044587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295389507/10000000000 : ℝ)^4463 ≤ (43821322747259/100000000000000 : ℝ)^3439 := by
    have hnat : (5295389507 : ℕ)^4463*100000000000000^3439 ≤ 43821322747259^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295389507 10000000000 43821322747259 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2717981501/5000000000 : ℝ)^4463 ≤ (9067387115487/20000000000000 : ℝ)^3439 := by
    have hnat : (2717981501 : ℕ)^4463*20000000000000^3439 ≤ 9067387115487^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717981501 5000000000 9067387115487 20000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1805044587/10000000000 : ℝ)^4463 ≤ (10841741666203/100000000000000 : ℝ)^3439 := by
    have hnat : (1805044587 : ℕ)^4463*100000000000000^3439 ≤ 10841741666203^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1805044587 10000000000 10841741666203 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295389507/10000000000 : ℝ), (2717981501/5000000000 : ℝ), (-1805044587/10000000000 : ℝ)] ![(43821322747259/100000000000000 : ℝ), (9067387115487/20000000000000 : ℝ), (10841741666203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295389507/10000000000 : ℝ)|^4463 ≤ (43821322747259/100000000000000 : ℝ)^3439
        have hw : |(5295389507/10000000000 : ℝ)|=(5295389507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2717981501/5000000000 : ℝ)|^4463 ≤ (9067387115487/20000000000000 : ℝ)^3439
        have hw : |(2717981501/5000000000 : ℝ)|=(2717981501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1805044587/10000000000 : ℝ)|^4463 ≤ (10841741666203/100000000000000 : ℝ)^3439
        have hw : |(-1805044587/10000000000 : ℝ)|=(1805044587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s5_7 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (856706339/2000000000 : ℝ)*x 0 + (906536367/2000000000 : ℝ)*x 1 + (809303221/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (856706339/2000000000 : ℝ)^4463 ≤ (33278748373031/100000000000000 : ℝ)^3439 := by
    have hnat : (856706339 : ℕ)^4463*100000000000000^3439 ≤ 33278748373031^3439*2000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      856706339 2000000000 33278748373031 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (906536367/2000000000 : ℝ)^4463 ≤ (4476527405713/12500000000000 : ℝ)^3439 := by
    have hnat : (906536367 : ℕ)^4463*12500000000000^3439 ≤ 4476527405713^3439*2000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906536367 2000000000 4476527405713 12500000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (809303221/2000000000 : ℝ)^4463 ≤ (30909032360041/100000000000000 : ℝ)^3439 := by
    have hnat : (809303221 : ℕ)^4463*100000000000000^3439 ≤ 30909032360041^3439*2000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      809303221 2000000000 30909032360041 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(856706339/2000000000 : ℝ), (906536367/2000000000 : ℝ), (809303221/2000000000 : ℝ)] ![(33278748373031/100000000000000 : ℝ), (4476527405713/12500000000000 : ℝ), (30909032360041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(856706339/2000000000 : ℝ)|^4463 ≤ (33278748373031/100000000000000 : ℝ)^3439
        have hw : |(856706339/2000000000 : ℝ)|=(856706339/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(906536367/2000000000 : ℝ)|^4463 ≤ (4476527405713/12500000000000 : ℝ)^3439
        have hw : |(906536367/2000000000 : ℝ)|=(906536367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(809303221/2000000000 : ℝ)|^4463 ≤ (30909032360041/100000000000000 : ℝ)^3439
        have hw : |(809303221/2000000000 : ℝ)|=(809303221/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1483_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161066273/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10787/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10797/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7739/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10787/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10787/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10787/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10787/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10787/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10787/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10787/100000 : ℝ) ^ (4461/1024 : ℝ) ≤ (1530469586846383/25000000000000000000 : ℝ) := by
    have hpowers : (10787/100000 : ℝ)^4461 ≤ (1530469586846383/25000000000000000000 : ℝ)^1024 := by
      have hnat : (10787 : ℕ)^4461*25000000000000000000^1024 ≤ 1530469586846383^1024*100000^4461 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10787 100000 1530469586846383 25000000000000000000 4461 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10787/100000 : ℝ)) (X := (1530469586846383/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15489/100000 : ℝ) ^ (4461/1024 : ℝ) ≤ (14803048221989969/50000000000000000000 : ℝ) := by
    have hpowers : (15489/100000 : ℝ)^4461 ≤ (14803048221989969/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15489 : ℕ)^4461*50000000000000000000^1024 ≤ 14803048221989969^1024*100000^4461 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15489 100000 14803048221989969 50000000000000000000 4461 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15489/100000 : ℝ)) (X := (14803048221989969/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501530469586846383/12500000000000000000 : ℝ) ≤ (5000140517995353/5000000000000000 : ℝ) ^ (4461/1024 : ℝ) := by
    have hpowers : (12501530469586846383/12500000000000000000 : ℝ)^1024 ≤ (5000140517995353/5000000000000000 : ℝ)^4461 := by
      have hnat : (12501530469586846383 : ℕ)^1024*5000000000000000^4461 ≤ 5000140517995353^4461*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501530469586846383 12500000000000000000 5000140517995353 5000000000000000 1024 4461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000140517995353/5000000000000000 : ℝ)) (X := (12501530469586846383/12500000000000000000 : ℝ)) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10003572797479136547/10000000000000000000 : ℝ) ≤ (5000410002374431/5000000000000000 : ℝ) ^ (4461/1024 : ℝ) := by
    have hpowers : (10003572797479136547/10000000000000000000 : ℝ)^1024 ≤ (5000410002374431/5000000000000000 : ℝ)^4461 := by
      have hnat : (10003572797479136547 : ℕ)^1024*5000000000000000^4461 ≤ 5000410002374431^4461*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003572797479136547 10000000000000000000 5000410002374431 5000000000000000 1024 4461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000410002374431/5000000000000000 : ℝ)) (X := (10003572797479136547/10000000000000000000 : ℝ)) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014803048221989969/25000000000000000000 : ℝ) ≤ (5000679486753509/5000000000000000 : ℝ) ^ (4461/1024 : ℝ) := by
    have hpowers : (25014803048221989969/25000000000000000000 : ℝ)^1024 ≤ (5000679486753509/5000000000000000 : ℝ)^4461 := by
      have hnat : (25014803048221989969 : ℕ)^1024*5000000000000000^4461 ≤ 5000679486753509^4461*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014803048221989969 25000000000000000000 5000679486753509 5000000000000000 1024 4461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000679486753509/5000000000000000 : ℝ)) (X := (25014803048221989969/25000000000000000000 : ℝ)) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1530469586846383/25000000000000000000 : ℝ) ≤ ((11752423429809960517/11755000000000000000 : ℝ)+2*(134742189539/117550000000000 : ℝ)*(10787/100000 : ℝ))^(4461/1024 : ℝ) := by
    rw [show (11752423429809960517/11755000000000000000 : ℝ)+2*(134742189539/117550000000000 : ℝ)*(10787/100000 : ℝ)=(5000140517995353/5000000000000000 : ℝ) by norm_num, show 1+2*(1530469586846383/25000000000000000000 : ℝ)=(12501530469586846383/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14803048221989969/50000000000000000000 : ℝ)+(1530469586846383/25000000000000000000 : ℝ) ≤ ((11752423429809960517/11755000000000000000 : ℝ)+(134742189539/117550000000000 : ℝ)*((15489/100000 : ℝ)+(10787/100000 : ℝ)))^(4461/1024 : ℝ) := by
    rw [show (11752423429809960517/11755000000000000000 : ℝ)+(134742189539/117550000000000 : ℝ)*((15489/100000 : ℝ)+(10787/100000 : ℝ))=(5000410002374431/5000000000000000 : ℝ) by norm_num, show 1+(14803048221989969/50000000000000000000 : ℝ)+(1530469586846383/25000000000000000000 : ℝ)=(10003572797479136547/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14803048221989969/50000000000000000000 : ℝ) ≤ ((11752423429809960517/11755000000000000000 : ℝ)+2*(134742189539/117550000000000 : ℝ)*(15489/100000 : ℝ))^(4461/1024 : ℝ) := by
    rw [show (11752423429809960517/11755000000000000000 : ℝ)+2*(134742189539/117550000000000 : ℝ)*(15489/100000 : ℝ)=(5000679486753509/5000000000000000 : ℝ) by norm_num, show 1+2*(14803048221989969/50000000000000000000 : ℝ)=(25014803048221989969/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11752423429809960517/11755000000000000000 : ℝ)*(X 1 0+X 2 0)+(134742189539/117550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4461/1024 : ℝ)) (lo := (10787/100000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (11752423429809960517/11755000000000000000 : ℝ)) (alpha := (134742189539/117550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11752423429809960517/11755000000000000000 : ℝ)*(X 0 1+X 2 1)+(134742189539/117550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4461/1024 : ℝ)) (lo := (10787/100000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (11752423429809960517/11755000000000000000 : ℝ)) (alpha := (134742189539/117550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11752423429809960517/11755000000000000000 : ℝ)*(X 0 2+X 1 2)+(134742189539/117550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4461/1024 : ℝ)) (lo := (10787/100000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (11752423429809960517/11755000000000000000 : ℝ)) (alpha := (134742189539/117550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-477928587/2500000000 : ℝ)*X 0 0+(2718551871/5000000000 : ℝ)*X 0 1+(65199597/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353171479/10000000000 : ℝ)*X 1 0+(-2025040143/10000000000 : ℝ)*X 1 1+(5215967681/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676585843/5000000000 : ℝ)*X 2 0+(1303991879/2500000000 : ℝ)*X 2 1+(-1012520043/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2141732337/5000000000 : ℝ)*X 0 0+(4043981519/10000000000 : ℝ)*X 0 1+(4535197691/10000000000 : ℝ)*X 0 2+(2141732337/5000000000 : ℝ)*X 1 0+(4043981519/10000000000 : ℝ)*X 1 1+(4535197691/10000000000 : ℝ)*X 1 2+(2141732337/5000000000 : ℝ)*X 2 0+(4043981519/10000000000 : ℝ)*X 2 1+(4535197691/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1911744639/10000000000 : ℝ)*X 0 0+(5217100121/10000000000 : ℝ)*X 0 1+(1087192607/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295389507/10000000000 : ℝ)*X 1 0+(-112815291/625000000 : ℝ)*X 1 1+(679495369/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295389507/10000000000 : ℝ)*X 2 0+(2717981501/5000000000 : ℝ)*X 2 1+(-1805044587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((856706339/2000000000 : ℝ)*X 0 0+(906536367/2000000000 : ℝ)*X 0 1+(809303221/2000000000 : ℝ)*X 0 2+(856706339/2000000000 : ℝ)*X 1 0+(906536367/2000000000 : ℝ)*X 1 1+(809303221/2000000000 : ℝ)*X 1 2+(856706339/2000000000 : ℝ)*X 2 0+(906536367/2000000000 : ℝ)*X 2 1+(809303221/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (620197576730787508451575089/58775000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (360816563/20000000000000 : ℝ)*(base19) + (269381/15625000000 : ℝ)*(base23) + (13645767/10000000000000 : ℝ)*(lower2) + (145678971/50000000000000 : ℝ)*(upper3) + (186493057/100000000000000 : ℝ)*(upper5) + (327897160113213/10000000000000 : ℝ)*(major0) + (327897160113213/10000000000000 : ℝ)*(major1) + (327897160113213/10000000000000 : ℝ)*(major2) + (4522128162440301/100000000000000 : ℝ)*(sp0) + (226107536116999/5000000000000 : ℝ)*(sp1) + (904430160476879/20000000000000 : ℝ)*(sp2) + (1017887859728159/50000000000000 : ℝ)*(sp3) + (12181991247/50000000000000 : ℝ)*(sp4) + (14604649667/100000000000000 : ℝ)*(sp7) + (407158064821197/20000000000000 : ℝ)*(f.failure) + (904430505284559/20000000000000 : ℝ)*(f.sum) + (1689382857461/470200000000000000000000000 : ℝ)*base66 + (44596406146938879/117550000000000000000000000000000 : ℝ)*base68 + (896737482232938879/117550000000000000000000000000000 : ℝ)*base70 + (1177726944402638879/117550000000000000000000000000000 : ℝ)*base72 + (4294679655931/2351000000000000000000000000 : ℝ)*base73 + (269300407574438879/117550000000000000000000000000000 : ℝ)*base76 + (651668307005138879/117550000000000000000000000000000 : ℝ)*base78 + (956469925102138879/117550000000000000000000000000000 : ℝ)*base80 + (37786702101/18808000000000000000000000 : ℝ)*base82 + (12188781/2000000000000000000000 : ℝ)*base89 + (12188781/2000000000000000000000 : ℝ)*base91 + (12188781/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28542745550641369708803/2938750000000000000000000000 : ℝ) := by norm_num
    linear_combination (1643812003/100000000000000 : ℝ)*(base19) + (1828903087/100000000000000 : ℝ)*(base23) + (198627879/100000000000000 : ℝ)*(upper3) + (482873/625000000000 : ℝ)*(lower4) + (25700901/12500000000000 : ℝ)*(upper5) + (1656495194412111/50000000000000 : ℝ)*(major0) + (1656495194412111/50000000000000 : ℝ)*(major1) + (1656495194412111/50000000000000 : ℝ)*(major2) + (11675040423/50000000000000 : ℝ)*(sp1) + (13470816901/50000000000000 : ℝ)*(sp2) + (1142267285525379/25000000000000 : ℝ)*(sp4) + (1142261037052167/25000000000000 : ℝ)*(sp5) + (4569040371564627/100000000000000 : ℝ)*(sp6) + (128556956987211/6250000000000 : ℝ)*(sp7) + (128556956987211/6250000000000 : ℝ)*(f.failure) + (1142267285525379/25000000000000 : ℝ)*(f.sum) + (1033637817599/183671875000000000000000000 : ℝ)*base65 + (1446235026370521387/587750000000000000000000000000000 : ℝ)*base67 + (1739260149015478613/587750000000000000000000000000000 : ℝ)*base70 + (1732611926562978613/587750000000000000000000000000000 : ℝ)*base72 + (30743946751973/5877500000000000000000000000 : ℝ)*base73 + (1379961426059021387/587750000000000000000000000000000 : ℝ)*base75 + (1679750368063228613/587750000000000000000000000000000 : ℝ)*base78 + (7849405313833021387/587750000000000000000000000000000 : ℝ)*base79 + (20073041813229/11755000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (3065397/625000000000000000000 : ℝ)*base90 + (3065397/625000000000000000000 : ℝ)*base92 + (3065397/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1483_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161066273/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10787/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10797/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1483_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1483_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161066273/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16117/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1021/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10797/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1483_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1483_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1483_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161066273/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16117/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1021/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10797/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1483_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
