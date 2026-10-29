-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1766_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:30:16.72771+00:00
-- url     : https://prove2.me/submissions/a4122ec2-f53e-4979-9ef4-06a3d5d87b3c

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
theorem support_rectangle_w1766_s3_0 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1138502309/10000000000 : ℝ)*x 0 + (2738153807/5000000000 : ℝ)*x 1 + (1271256673/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1138502309/10000000000 : ℝ)^6031 ≤ (7300309814989/100000000000000 : ℝ)^5007 := by
    have hnat : (1138502309 : ℕ)^6031*100000000000000^5007 ≤ 7300309814989^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1138502309 10000000000 7300309814989 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2738153807/5000000000 : ℝ)^6031 ≤ (48417796398133/100000000000000 : ℝ)^5007 := by
    have hnat : (2738153807 : ℕ)^6031*100000000000000^5007 ≤ 48417796398133^5007*5000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2738153807 5000000000 48417796398133 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1271256673/2500000000 : ℝ)^6031 ≤ (22140946884339/50000000000000 : ℝ)^5007 := by
    have hnat : (1271256673 : ℕ)^6031*50000000000000^5007 ≤ 22140946884339^5007*2500000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1271256673 2500000000 22140946884339 50000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1138502309/10000000000 : ℝ), (2738153807/5000000000 : ℝ), (1271256673/2500000000 : ℝ)] ![(7300309814989/100000000000000 : ℝ), (48417796398133/100000000000000 : ℝ), (22140946884339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1138502309/10000000000 : ℝ)|^6031 ≤ (7300309814989/100000000000000 : ℝ)^5007
        have hw : |(-1138502309/10000000000 : ℝ)|=(1138502309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2738153807/5000000000 : ℝ)|^6031 ≤ (48417796398133/100000000000000 : ℝ)^5007
        have hw : |(2738153807/5000000000 : ℝ)|=(2738153807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1271256673/2500000000 : ℝ)|^6031 ≤ (22140946884339/50000000000000 : ℝ)^5007
        have hw : |(1271256673/2500000000 : ℝ)|=(1271256673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_s3_1 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2662613879/5000000000 : ℝ)*x 0 + (-1342644839/10000000000 : ℝ)*x 1 + (2542513471/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2662613879/5000000000 : ℝ)^6031 ≤ (936268900949/2000000000000 : ℝ)^5007 := by
    have hnat : (2662613879 : ℕ)^6031*2000000000000^5007 ≤ 936268900949^5007*5000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2662613879 5000000000 936268900949 2000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1342644839/10000000000 : ℝ)^6031 ≤ (278270579711/3125000000000 : ℝ)^5007 := by
    have hnat : (1342644839 : ℕ)^6031*3125000000000^5007 ≤ 278270579711^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342644839 10000000000 278270579711 3125000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2542513471/5000000000 : ℝ)^6031 ≤ (2767618524437/6250000000000 : ℝ)^5007 := by
    have hnat : (2542513471 : ℕ)^6031*6250000000000^5007 ≤ 2767618524437^5007*5000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2542513471 5000000000 2767618524437 6250000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2662613879/5000000000 : ℝ), (-1342644839/10000000000 : ℝ), (2542513471/5000000000 : ℝ)] ![(936268900949/2000000000000 : ℝ), (278270579711/3125000000000 : ℝ), (2767618524437/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2662613879/5000000000 : ℝ)|^6031 ≤ (936268900949/2000000000000 : ℝ)^5007
        have hw : |(2662613879/5000000000 : ℝ)|=(2662613879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1342644839/10000000000 : ℝ)|^6031 ≤ (278270579711/3125000000000 : ℝ)^5007
        have hw : |(-1342644839/10000000000 : ℝ)|=(1342644839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2542513471/5000000000 : ℝ)|^6031 ≤ (2767618524437/6250000000000 : ℝ)^5007
        have hw : |(2542513471/5000000000 : ℝ)|=(2542513471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_s3_2 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (266261361/500000000 : ℝ)*x 0 + (508502707/1000000000 : ℝ)*x 1 + (-167830673/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (266261361/500000000 : ℝ)^6031 ≤ (46813439350709/100000000000000 : ℝ)^5007 := by
    have hnat : (266261361 : ℕ)^6031*100000000000000^5007 ≤ 46813439350709^5007*500000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266261361 500000000 46813439350709 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (508502707/1000000000 : ℝ)^6031 ≤ (44281897733617/100000000000000 : ℝ)^5007 := by
    have hnat : (508502707 : ℕ)^6031*100000000000000^5007 ≤ 44281897733617^5007*1000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508502707 1000000000 44281897733617 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (167830673/1250000000 : ℝ)^6031 ≤ (8904662904511/100000000000000 : ℝ)^5007 := by
    have hnat : (167830673 : ℕ)^6031*100000000000000^5007 ≤ 8904662904511^5007*1250000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167830673 1250000000 8904662904511 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(266261361/500000000 : ℝ), (508502707/1000000000 : ℝ), (-167830673/1250000000 : ℝ)] ![(46813439350709/100000000000000 : ℝ), (44281897733617/100000000000000 : ℝ), (8904662904511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(266261361/500000000 : ℝ)|^6031 ≤ (46813439350709/100000000000000 : ℝ)^5007
        have hw : |(266261361/500000000 : ℝ)|=(266261361/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(508502707/1000000000 : ℝ)|^6031 ≤ (44281897733617/100000000000000 : ℝ)^5007
        have hw : |(508502707/1000000000 : ℝ)|=(508502707/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-167830673/1250000000 : ℝ)|^6031 ≤ (8904662904511/100000000000000 : ℝ)^5007
        have hw : |(-167830673/1250000000 : ℝ)|=(167830673/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_s3_3 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3989043157/10000000000 : ℝ)*x 0 + (3333908413/10000000000 : ℝ)*x 1 + (4703711953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3989043157/10000000000 : ℝ)^6031 ≤ (8263821721693/25000000000000 : ℝ)^5007 := by
    have hnat : (3989043157 : ℕ)^6031*25000000000000^5007 ≤ 8263821721693^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3989043157 10000000000 8263821721693 25000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3333908413/10000000000 : ℝ)^6031 ≤ (26631226179659/100000000000000 : ℝ)^5007 := by
    have hnat : (3333908413 : ℕ)^6031*100000000000000^5007 ≤ 26631226179659^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3333908413 10000000000 26631226179659 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4703711953/10000000000 : ℝ)^6031 ≤ (40313486916311/100000000000000 : ℝ)^5007 := by
    have hnat : (4703711953 : ℕ)^6031*100000000000000^5007 ≤ 40313486916311^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4703711953 10000000000 40313486916311 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3989043157/10000000000 : ℝ), (3333908413/10000000000 : ℝ), (4703711953/10000000000 : ℝ)] ![(8263821721693/25000000000000 : ℝ), (26631226179659/100000000000000 : ℝ), (40313486916311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3989043157/10000000000 : ℝ)|^6031 ≤ (8263821721693/25000000000000 : ℝ)^5007
        have hw : |(3989043157/10000000000 : ℝ)|=(3989043157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3333908413/10000000000 : ℝ)|^6031 ≤ (26631226179659/100000000000000 : ℝ)^5007
        have hw : |(3333908413/10000000000 : ℝ)|=(3333908413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4703711953/10000000000 : ℝ)|^6031 ≤ (40313486916311/100000000000000 : ℝ)^5007
        have hw : |(4703711953/10000000000 : ℝ)|=(4703711953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_s3_4 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-227764493/2000000000 : ℝ)*x 0 + (2545777391/5000000000 : ℝ)*x 1 + (43757151/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (227764493/2000000000 : ℝ)^6031 ≤ (3651391319603/50000000000000 : ℝ)^5007 := by
    have hnat : (227764493 : ℕ)^6031*50000000000000^5007 ≤ 3651391319603^5007*2000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227764493 2000000000 3651391319603 50000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2545777391/5000000000 : ℝ)^6031 ≤ (44350377562071/100000000000000 : ℝ)^5007 := by
    have hnat : (2545777391 : ℕ)^6031*100000000000000^5007 ≤ 44350377562071^5007*5000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2545777391 5000000000 44350377562071 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43757151/80000000 : ℝ)^6031 ≤ (24173419895541/50000000000000 : ℝ)^5007 := by
    have hnat : (43757151 : ℕ)^6031*50000000000000^5007 ≤ 24173419895541^5007*80000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43757151 80000000 24173419895541 50000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-227764493/2000000000 : ℝ), (2545777391/5000000000 : ℝ), (43757151/80000000 : ℝ)] ![(3651391319603/50000000000000 : ℝ), (44350377562071/100000000000000 : ℝ), (24173419895541/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-227764493/2000000000 : ℝ)|^6031 ≤ (3651391319603/50000000000000 : ℝ)^5007
        have hw : |(-227764493/2000000000 : ℝ)|=(227764493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2545777391/5000000000 : ℝ)|^6031 ≤ (44350377562071/100000000000000 : ℝ)^5007
        have hw : |(2545777391/5000000000 : ℝ)|=(2545777391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43757151/80000000 : ℝ)|^6031 ≤ (24173419895541/50000000000000 : ℝ)^5007
        have hw : |(43757151/80000000 : ℝ)|=(43757151/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_s3_5 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1305513429/2500000000 : ℝ)*x 0 + (-479014247/5000000000 : ℝ)*x 1 + (5469643807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1305513429/2500000000 : ℝ)^6031 ≤ (45723137900163/100000000000000 : ℝ)^5007 := by
    have hnat : (1305513429 : ℕ)^6031*100000000000000^5007 ≤ 45723137900163^5007*2500000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305513429 2500000000 45723137900163 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (479014247/5000000000 : ℝ)^6031 ≤ (5930023012897/100000000000000 : ℝ)^5007 := by
    have hnat : (479014247 : ℕ)^6031*100000000000000^5007 ≤ 5930023012897^5007*5000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      479014247 5000000000 5930023012897 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5469643807/10000000000 : ℝ)^6031 ≤ (48346839067097/100000000000000 : ℝ)^5007 := by
    have hnat : (5469643807 : ℕ)^6031*100000000000000^5007 ≤ 48346839067097^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469643807 10000000000 48346839067097 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1305513429/2500000000 : ℝ), (-479014247/5000000000 : ℝ), (5469643807/10000000000 : ℝ)] ![(45723137900163/100000000000000 : ℝ), (5930023012897/100000000000000 : ℝ), (48346839067097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1305513429/2500000000 : ℝ)|^6031 ≤ (45723137900163/100000000000000 : ℝ)^5007
        have hw : |(1305513429/2500000000 : ℝ)|=(1305513429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-479014247/5000000000 : ℝ)|^6031 ≤ (5930023012897/100000000000000 : ℝ)^5007
        have hw : |(-479014247/5000000000 : ℝ)|=(479014247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5469643807/10000000000 : ℝ)|^6031 ≤ (48346839067097/100000000000000 : ℝ)^5007
        have hw : |(5469643807/10000000000 : ℝ)|=(5469643807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_s3_6 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (104441073/200000000 : ℝ)*x 0 + (27348219/50000000 : ℝ)*x 1 + (-479014299/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104441073/200000000 : ℝ)^6031 ≤ (45723137204097/100000000000000 : ℝ)^5007 := by
    have hnat : (104441073 : ℕ)^6031*100000000000000^5007 ≤ 45723137204097^5007*200000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104441073 200000000 45723137204097 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27348219/50000000 : ℝ)^6031 ≤ (48346838992569/100000000000000 : ℝ)^5007 := by
    have hnat : (27348219 : ℕ)^6031*100000000000000^5007 ≤ 48346838992569^5007*50000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27348219 50000000 48346838992569 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (479014299/5000000000 : ℝ)^6031 ≤ (1482505947073/25000000000000 : ℝ)^5007 := by
    have hnat : (479014299 : ℕ)^6031*25000000000000^5007 ≤ 1482505947073^5007*5000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      479014299 5000000000 1482505947073 25000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(104441073/200000000 : ℝ), (27348219/50000000 : ℝ), (-479014299/5000000000 : ℝ)] ![(45723137204097/100000000000000 : ℝ), (48346838992569/100000000000000 : ℝ), (1482505947073/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(104441073/200000000 : ℝ)|^6031 ≤ (45723137204097/100000000000000 : ℝ)^5007
        have hw : |(104441073/200000000 : ℝ)|=(104441073/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(27348219/50000000 : ℝ)|^6031 ≤ (48346838992569/100000000000000 : ℝ)^5007
        have hw : |(27348219/50000000 : ℝ)|=(27348219/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-479014299/5000000000 : ℝ)|^6031 ≤ (1482505947073/25000000000000 : ℝ)^5007
        have hw : |(-479014299/5000000000 : ℝ)|=(479014299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_s3_7 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (159606567/400000000 : ℝ)*x 0 + (936171573/2000000000 : ℝ)*x 1 + (1678618743/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (159606567/400000000 : ℝ)^6031 ≤ (1653323817171/5000000000000 : ℝ)^5007 := by
    have hnat : (159606567 : ℕ)^6031*5000000000000^5007 ≤ 1653323817171^5007*400000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159606567 400000000 1653323817171 5000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (936171573/2000000000 : ℝ)^6031 ≤ (20038836570497/50000000000000 : ℝ)^5007 := by
    have hnat : (936171573 : ℕ)^6031*50000000000000^5007 ≤ 20038836570497^5007*2000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936171573 2000000000 20038836570497 50000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1678618743/5000000000 : ℝ)^6031 ≤ (26855850506407/100000000000000 : ℝ)^5007 := by
    have hnat : (1678618743 : ℕ)^6031*100000000000000^5007 ≤ 26855850506407^5007*5000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1678618743 5000000000 26855850506407 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(159606567/400000000 : ℝ), (936171573/2000000000 : ℝ), (1678618743/5000000000 : ℝ)] ![(1653323817171/5000000000000 : ℝ), (20038836570497/50000000000000 : ℝ), (26855850506407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(159606567/400000000 : ℝ)|^6031 ≤ (1653323817171/5000000000000 : ℝ)^5007
        have hw : |(159606567/400000000 : ℝ)|=(159606567/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(936171573/2000000000 : ℝ)|^6031 ≤ (20038836570497/50000000000000 : ℝ)^5007
        have hw : |(936171573/2000000000 : ℝ)|=(936171573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1678618743/5000000000 : ℝ)|^6031 ≤ (26855850506407/100000000000000 : ℝ)^5007
        have hw : |(1678618743/5000000000 : ℝ)|=(1678618743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1766_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11252043/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4417/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4607/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1843/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17667/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4417/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4607/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4417/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4607/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4417/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4607/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4417/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4607/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4417/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4607/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4417/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4607/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4607/50000 : ℝ) ^ (6015/1024 : ℝ) ≤ (8263128424469/10000000000000000000 : ℝ) := by
    have hpowers : (4607/50000 : ℝ)^6015 ≤ (8263128424469/10000000000000000000 : ℝ)^1024 := by
      have hnat : (4607 : ℕ)^6015*10000000000000000000^1024 ≤ 8263128424469^1024*50000^6015 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4607 50000 8263128424469 10000000000000000000 6015 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4607/50000 : ℝ)) (X := (8263128424469/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6015 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4417/25000 : ℝ) ^ (6015/1024 : ℝ) ≤ (473010848363077/12500000000000000000 : ℝ) := by
    have hpowers : (4417/25000 : ℝ)^6015 ≤ (473010848363077/12500000000000000000 : ℝ)^1024 := by
      have hnat : (4417 : ℕ)^6015*12500000000000000000^1024 ≤ 473010848363077^1024*25000^6015 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4417 25000 473010848363077 12500000000000000000 6015 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4417/25000 : ℝ)) (X := (473010848363077/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 6015 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000008263128424469/5000000000000000000 : ℝ) ≤ (10000002813445621/10000000000000000 : ℝ) ^ (6015/1024 : ℝ) := by
    have hpowers : (5000008263128424469/5000000000000000000 : ℝ)^1024 ≤ (10000002813445621/10000000000000000 : ℝ)^6015 := by
      have hnat : (5000008263128424469 : ℕ)^1024*10000000000000000^6015 ≤ 10000002813445621^6015*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000008263128424469 5000000000000000000 10000002813445621 10000000000000000 1024 6015 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000002813445621/10000000000000000 : ℝ)) (X := (5000008263128424469/5000000000000000000 : ℝ)) (by norm_num) 6015 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50001933359035574653/50000000000000000000 : ℝ) ≤ (312502057073871/312500000000000 : ℝ) ^ (6015/1024 : ℝ) := by
    have hpowers : (50001933359035574653/50000000000000000000 : ℝ)^1024 ≤ (312502057073871/312500000000000 : ℝ)^6015 := by
      have hnat : (50001933359035574653 : ℕ)^1024*312500000000000^6015 ≤ 312502057073871^6015*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001933359035574653 50000000000000000000 312502057073871 312500000000000 1024 6015 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312502057073871/312500000000000 : ℝ)) (X := (50001933359035574653/50000000000000000000 : ℝ)) (by norm_num) 6015 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6250473010848363077/6250000000000000000 : ℝ) ≤ (10000128839282123/10000000000000000 : ℝ) ^ (6015/1024 : ℝ) := by
    have hpowers : (6250473010848363077/6250000000000000000 : ℝ)^1024 ≤ (10000128839282123/10000000000000000 : ℝ)^6015 := by
      have hnat : (6250473010848363077 : ℕ)^1024*10000000000000000^6015 ≤ 10000128839282123^6015*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250473010848363077 6250000000000000000 10000128839282123 10000000000000000 1024 6015 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000128839282123/10000000000000000 : ℝ)) (X := (6250473010848363077/6250000000000000000 : ℝ)) (by norm_num) 6015 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8263128424469/10000000000000000000 : ℝ) ≤ ((42269431291405875253/42270000000000000000 : ℝ)+2*(63012918251/845400000000000 : ℝ)*(4607/50000 : ℝ))^(6015/1024 : ℝ) := by
    rw [show (42269431291405875253/42270000000000000000 : ℝ)+2*(63012918251/845400000000000 : ℝ)*(4607/50000 : ℝ)=(10000002813445621/10000000000000000 : ℝ) by norm_num, show 1+2*(8263128424469/10000000000000000000 : ℝ)=(5000008263128424469/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(473010848363077/12500000000000000000 : ℝ)+(8263128424469/10000000000000000000 : ℝ) ≤ ((42269431291405875253/42270000000000000000 : ℝ)+(63012918251/845400000000000 : ℝ)*((4417/25000 : ℝ)+(4607/50000 : ℝ)))^(6015/1024 : ℝ) := by
    rw [show (42269431291405875253/42270000000000000000 : ℝ)+(63012918251/845400000000000 : ℝ)*((4417/25000 : ℝ)+(4607/50000 : ℝ))=(312502057073871/312500000000000 : ℝ) by norm_num, show 1+(473010848363077/12500000000000000000 : ℝ)+(8263128424469/10000000000000000000 : ℝ)=(50001933359035574653/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(473010848363077/12500000000000000000 : ℝ) ≤ ((42269431291405875253/42270000000000000000 : ℝ)+2*(63012918251/845400000000000 : ℝ)*(4417/25000 : ℝ))^(6015/1024 : ℝ) := by
    rw [show (42269431291405875253/42270000000000000000 : ℝ)+2*(63012918251/845400000000000 : ℝ)*(4417/25000 : ℝ)=(10000128839282123/10000000000000000 : ℝ) by norm_num, show 1+2*(473010848363077/12500000000000000000 : ℝ)=(6250473010848363077/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (42269431291405875253/42270000000000000000 : ℝ)*(X 1 0+X 2 0)+(63012918251/845400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6015/1024 : ℝ)) (lo := (4607/50000 : ℝ)) (hi := (4417/25000 : ℝ)) (c := (42269431291405875253/42270000000000000000 : ℝ)) (alpha := (63012918251/845400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (42269431291405875253/42270000000000000000 : ℝ)*(X 0 1+X 2 1)+(63012918251/845400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6015/1024 : ℝ)) (lo := (4607/50000 : ℝ)) (hi := (4417/25000 : ℝ)) (c := (42269431291405875253/42270000000000000000 : ℝ)) (alpha := (63012918251/845400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (42269431291405875253/42270000000000000000 : ℝ)*(X 0 2+X 1 2)+(63012918251/845400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6015/1024 : ℝ)) (lo := (4607/50000 : ℝ)) (hi := (4417/25000 : ℝ)) (c := (42269431291405875253/42270000000000000000 : ℝ)) (alpha := (63012918251/845400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1138502309/10000000000 : ℝ)*X 0 0+(2738153807/5000000000 : ℝ)*X 0 1+(1271256673/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2662613879/5000000000 : ℝ)*X 1 0+(-1342644839/10000000000 : ℝ)*X 1 1+(2542513471/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((266261361/500000000 : ℝ)*X 2 0+(508502707/1000000000 : ℝ)*X 2 1+(-167830673/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((3989043157/10000000000 : ℝ)*X 0 0+(3333908413/10000000000 : ℝ)*X 0 1+(4703711953/10000000000 : ℝ)*X 0 2+(3989043157/10000000000 : ℝ)*X 1 0+(3333908413/10000000000 : ℝ)*X 1 1+(4703711953/10000000000 : ℝ)*X 1 2+(3989043157/10000000000 : ℝ)*X 2 0+(3333908413/10000000000 : ℝ)*X 2 1+(4703711953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-227764493/2000000000 : ℝ)*X 0 0+(2545777391/5000000000 : ℝ)*X 0 1+(43757151/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1305513429/2500000000 : ℝ)*X 1 0+(-479014247/5000000000 : ℝ)*X 1 1+(5469643807/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((104441073/200000000 : ℝ)*X 2 0+(27348219/50000000 : ℝ)*X 2 1+(-479014299/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((159606567/400000000 : ℝ)*X 0 0+(936171573/2000000000 : ℝ)*X 0 1+(1678618743/5000000000 : ℝ)*X 0 2+(159606567/400000000 : ℝ)*X 1 0+(936171573/2000000000 : ℝ)*X 1 1+(1678618743/5000000000 : ℝ)*X 1 2+(159606567/400000000 : ℝ)*X 2 0+(936171573/2000000000 : ℝ)*X 2 1+(1678618743/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6142043387405618423863/2818000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29640321/5000000000000 : ℝ)*(base19) + (36078867/12500000000000 : ℝ)*(base23) + (95368943/100000000000000 : ℝ)*(upper3) + (2435071/50000000000000 : ℝ)*(lower4) + (328576061441129/20000000000000 : ℝ)*(major0) + (328576061441129/20000000000000 : ℝ)*(major1) + (328576061441129/20000000000000 : ℝ)*(major2) + (2555717333925241/100000000000000 : ℝ)*(sp0) + (159732718634193/6250000000000 : ℝ)*(sp1) + (319465119669027/12500000000000 : ℝ)*(sp2) + (730033940511319/100000000000000 : ℝ)*(sp3) + (6757028267/100000000000000 : ℝ)*(sp4) + (2844970357/100000000000000 : ℝ)*(sp6) + (1255146973/50000000000000 : ℝ)*(sp7) + (146007290161053/20000000000000 : ℝ)*(f.failure) + (638931022738377/25000000000000 : ℝ)*(f.sum) + (21969191796707/8454000000000000000000000000 : ℝ)*base66 + (4533211764899430637/845400000000000000000000000000000 : ℝ)*base67 + (7940695076582430637/845400000000000000000000000000000 : ℝ)*base69 + (525262410653369363/845400000000000000000000000000000 : ℝ)*base72 + (10054582369691/8454000000000000000000000000 : ℝ)*base74 + (9510689530927830637/845400000000000000000000000000000 : ℝ)*base75 + (2300352058969769363/845400000000000000000000000000000 : ℝ)*base78 + (103989800921369363/845400000000000000000000000000000 : ℝ)*base80 + (10289274320197/8454000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (281279/100000000000000000000 : ℝ)*base89 + (281279/100000000000000000000 : ℝ)*base91 + (281279/100000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (41908353139767271637971/14090000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17890227/5000000000000 : ℝ)*(base19) + (355742021/100000000000000 : ℝ)*(base23) + (71067577/100000000000000 : ℝ)*(lower1) + (46138989/100000000000000 : ℝ)*(upper3) + (2359683/10000000000000 : ℝ)*(lower4) + (71825921/100000000000000 : ℝ)*(upper5) + (1700190205875161/100000000000000 : ℝ)*(major0) + (1700190205875161/100000000000000 : ℝ)*(major1) + (1700190205875161/100000000000000 : ℝ)*(major2) + (349782759/50000000000000 : ℝ)*(sp1) + (165304838776939/6250000000000 : ℝ)*(sp4) + (1322438181530483/50000000000000 : ℝ)*(sp5) + (2644877064689003/100000000000000 : ℝ)*(sp6) + (188875723043713/25000000000000 : ℝ)*(sp7) + (188875723043713/25000000000000 : ℝ)*(f.failure) + (165304838776939/6250000000000 : ℝ)*(f.sum) + (93962254289611/42270000000000000000000000000 : ℝ)*base65 + (5514673093568159267/4227000000000000000000000000000000 : ℝ)*base68 + (3397420887116159267/4227000000000000000000000000000000 : ℝ)*base70 + (22215894011427840733/4227000000000000000000000000000000 : ℝ)*base71 + (74906870571569/42270000000000000000000000000 : ℝ)*base74 + (27510633408297840733/4227000000000000000000000000000000 : ℝ)*base75 + (36575382239877840733/4227000000000000000000000000000000 : ℝ)*base77 + (3142373463032159267/4227000000000000000000000000000000 : ℝ)*base80 + (167208069667649/42270000000000000000000000000 : ℝ)*base82 + (1694341/125000000000000000000 : ℝ)*base90 + (1694341/125000000000000000000 : ℝ)*base92 + (1694341/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1766_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11252043/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4417/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4607/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1843/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17667/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1766_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1766_box_0 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-388299039/5000000000 : ℝ)*x 0 + (540858671/1000000000 : ℝ)*x 1 + (1081717331/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (388299039/5000000000 : ℝ)^6031 ≤ (4604964367047/100000000000000 : ℝ)^5007 := by
    have hnat : (388299039 : ℕ)^6031*100000000000000^5007 ≤ 4604964367047^5007*5000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388299039 5000000000 4604964367047 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540858671/1000000000 : ℝ)^6031 ≤ (238487590483/500000000000 : ℝ)^5007 := by
    have hnat : (540858671 : ℕ)^6031*500000000000^5007 ≤ 238487590483^5007*1000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540858671 1000000000 238487590483 500000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081717331/2000000000 : ℝ)^6031 ≤ (23848758756183/50000000000000 : ℝ)^5007 := by
    have hnat : (1081717331 : ℕ)^6031*50000000000000^5007 ≤ 23848758756183^5007*2000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081717331 2000000000 23848758756183 50000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-388299039/5000000000 : ℝ), (540858671/1000000000 : ℝ), (1081717331/2000000000 : ℝ)] ![(4604964367047/100000000000000 : ℝ), (238487590483/500000000000 : ℝ), (23848758756183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-388299039/5000000000 : ℝ)|^6031 ≤ (4604964367047/100000000000000 : ℝ)^5007
        have hw : |(-388299039/5000000000 : ℝ)|=(388299039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540858671/1000000000 : ℝ)|^6031 ≤ (238487590483/500000000000 : ℝ)^5007
        have hw : |(540858671/1000000000 : ℝ)|=(540858671/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081717331/2000000000 : ℝ)|^6031 ≤ (23848758756183/50000000000000 : ℝ)^5007
        have hw : |(1081717331/2000000000 : ℝ)|=(1081717331/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_box_1 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1298109587/2500000000 : ℝ)*x 0 + (-135664339/1250000000 : ℝ)*x 1 + (1352146717/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1298109587/2500000000 : ℝ)^6031 ≤ (22705491105571/50000000000000 : ℝ)^5007 := by
    have hnat : (1298109587 : ℕ)^6031*50000000000000^5007 ≤ 22705491105571^5007*2500000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298109587 2500000000 22705491105571 50000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135664339/1250000000 : ℝ)^6031 ≤ (3445748999227/50000000000000 : ℝ)^5007 := by
    have hnat : (135664339 : ℕ)^6031*50000000000000^5007 ≤ 3445748999227^5007*1250000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135664339 1250000000 3445748999227 50000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352146717/2500000000 : ℝ)^6031 ≤ (47697519774943/100000000000000 : ℝ)^5007 := by
    have hnat : (1352146717 : ℕ)^6031*100000000000000^5007 ≤ 47697519774943^5007*2500000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352146717 2500000000 47697519774943 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1298109587/2500000000 : ℝ), (-135664339/1250000000 : ℝ), (1352146717/2500000000 : ℝ)] ![(22705491105571/50000000000000 : ℝ), (3445748999227/50000000000000 : ℝ), (47697519774943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1298109587/2500000000 : ℝ)|^6031 ≤ (22705491105571/50000000000000 : ℝ)^5007
        have hw : |(1298109587/2500000000 : ℝ)|=(1298109587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-135664339/1250000000 : ℝ)|^6031 ≤ (3445748999227/50000000000000 : ℝ)^5007
        have hw : |(-135664339/1250000000 : ℝ)|=(135664339/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352146717/2500000000 : ℝ)|^6031 ≤ (47697519774943/100000000000000 : ℝ)^5007
        have hw : |(1352146717/2500000000 : ℝ)|=(1352146717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_box_2 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2596219043/5000000000 : ℝ)*x 0 + (5408586991/10000000000 : ℝ)*x 1 + (-542657451/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2596219043/5000000000 : ℝ)^6031 ≤ (45410979451183/100000000000000 : ℝ)^5007 := by
    have hnat : (2596219043 : ℕ)^6031*100000000000000^5007 ≤ 45410979451183^5007*5000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596219043 5000000000 45410979451183 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408586991/10000000000 : ℝ)^6031 ≤ (47697521081501/100000000000000 : ℝ)^5007 := by
    have hnat : (5408586991 : ℕ)^6031*100000000000000^5007 ≤ 47697521081501^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408586991 10000000000 47697521081501 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542657451/5000000000 : ℝ)^6031 ≤ (6891499451647/100000000000000 : ℝ)^5007 := by
    have hnat : (542657451 : ℕ)^6031*100000000000000^5007 ≤ 6891499451647^5007*5000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542657451 5000000000 6891499451647 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2596219043/5000000000 : ℝ), (5408586991/10000000000 : ℝ), (-542657451/5000000000 : ℝ)] ![(45410979451183/100000000000000 : ℝ), (47697521081501/100000000000000 : ℝ), (6891499451647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2596219043/5000000000 : ℝ)|^6031 ≤ (45410979451183/100000000000000 : ℝ)^5007
        have hw : |(2596219043/5000000000 : ℝ)|=(2596219043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408586991/10000000000 : ℝ)|^6031 ≤ (47697521081501/100000000000000 : ℝ)^5007
        have hw : |(5408586991/10000000000 : ℝ)|=(5408586991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-542657451/5000000000 : ℝ)|^6031 ≤ (6891499451647/100000000000000 : ℝ)^5007
        have hw : |(-542657451/5000000000 : ℝ)|=(542657451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_box_3 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (451307081/1000000000 : ℝ)*x 0 + (3764094461/10000000000 : ℝ)*x 1 + (1882046641/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (451307081/1000000000 : ℝ)^6031 ≤ (1917683709847/5000000000000 : ℝ)^5007 := by
    have hnat : (451307081 : ℕ)^6031*5000000000000^5007 ≤ 1917683709847^5007*1000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451307081 1000000000 1917683709847 5000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3764094461/10000000000 : ℝ)^6031 ≤ (30823168706723/100000000000000 : ℝ)^5007 := by
    have hnat : (3764094461 : ℕ)^6031*100000000000000^5007 ≤ 30823168706723^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3764094461 10000000000 30823168706723 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1882046641/5000000000 : ℝ)^6031 ≤ (1232926283109/4000000000000 : ℝ)^5007 := by
    have hnat : (1882046641 : ℕ)^6031*4000000000000^5007 ≤ 1232926283109^5007*5000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1882046641 5000000000 1232926283109 4000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(451307081/1000000000 : ℝ), (3764094461/10000000000 : ℝ), (1882046641/5000000000 : ℝ)] ![(1917683709847/5000000000000 : ℝ), (30823168706723/100000000000000 : ℝ), (1232926283109/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(451307081/1000000000 : ℝ)|^6031 ≤ (1917683709847/5000000000000 : ℝ)^5007
        have hw : |(451307081/1000000000 : ℝ)|=(451307081/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3764094461/10000000000 : ℝ)|^6031 ≤ (30823168706723/100000000000000 : ℝ)^5007
        have hw : |(3764094461/10000000000 : ℝ)|=(3764094461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1882046641/5000000000 : ℝ)|^6031 ≤ (1232926283109/4000000000000 : ℝ)^5007
        have hw : |(1882046641/5000000000 : ℝ)|=(1882046641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_box_4 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-61561591/400000000 : ℝ)*x 0 + (2564897951/5000000000 : ℝ)*x 1 + (5129795551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (61561591/400000000 : ℝ)^6031 ≤ (5248090580193/50000000000000 : ℝ)^5007 := by
    have hnat : (61561591 : ℕ)^6031*50000000000000^5007 ≤ 5248090580193^5007*400000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61561591 400000000 5248090580193 50000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2564897951/5000000000 : ℝ)^6031 ≤ (4475191125981/10000000000000 : ℝ)^5007 := by
    have hnat : (2564897951 : ℕ)^6031*10000000000000^5007 ≤ 4475191125981^5007*5000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564897951 5000000000 4475191125981 10000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5129795551/10000000000 : ℝ)^6031 ≤ (1790076302859/4000000000000 : ℝ)^5007 := by
    have hnat : (5129795551 : ℕ)^6031*4000000000000^5007 ≤ 1790076302859^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129795551 10000000000 1790076302859 4000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-61561591/400000000 : ℝ), (2564897951/5000000000 : ℝ), (5129795551/10000000000 : ℝ)] ![(5248090580193/50000000000000 : ℝ), (4475191125981/10000000000000 : ℝ), (1790076302859/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-61561591/400000000 : ℝ)|^6031 ≤ (5248090580193/50000000000000 : ℝ)^5007
        have hw : |(-61561591/400000000 : ℝ)|=(61561591/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2564897951/5000000000 : ℝ)|^6031 ≤ (4475191125981/10000000000000 : ℝ)^5007
        have hw : |(2564897951/5000000000 : ℝ)|=(2564897951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5129795551/10000000000 : ℝ)|^6031 ≤ (1790076302859/4000000000000 : ℝ)^5007
        have hw : |(5129795551/10000000000 : ℝ)|=(5129795551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_box_5 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075568567/2000000000 : ℝ)*x 0 + (-606338647/5000000000 : ℝ)*x 1 + (2564897739/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075568567/2000000000 : ℝ)^6031 ≤ (47371133663923/100000000000000 : ℝ)^5007 := by
    have hnat : (1075568567 : ℕ)^6031*100000000000000^5007 ≤ 47371133663923^5007*2000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075568567 2000000000 47371133663923 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (606338647/5000000000 : ℝ)^6031 ≤ (3938479760177/50000000000000 : ℝ)^5007 := by
    have hnat : (606338647 : ℕ)^6031*50000000000000^5007 ≤ 3938479760177^5007*5000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      606338647 5000000000 3938479760177 50000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2564897739/5000000000 : ℝ)^6031 ≤ (22375953402193/50000000000000 : ℝ)^5007 := by
    have hnat : (2564897739 : ℕ)^6031*50000000000000^5007 ≤ 22375953402193^5007*5000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564897739 5000000000 22375953402193 50000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075568567/2000000000 : ℝ), (-606338647/5000000000 : ℝ), (2564897739/5000000000 : ℝ)] ![(47371133663923/100000000000000 : ℝ), (3938479760177/50000000000000 : ℝ), (22375953402193/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075568567/2000000000 : ℝ)|^6031 ≤ (47371133663923/100000000000000 : ℝ)^5007
        have hw : |(1075568567/2000000000 : ℝ)|=(1075568567/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-606338647/5000000000 : ℝ)|^6031 ≤ (3938479760177/50000000000000 : ℝ)^5007
        have hw : |(-606338647/5000000000 : ℝ)|=(606338647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2564897739/5000000000 : ℝ)|^6031 ≤ (22375953402193/50000000000000 : ℝ)^5007
        have hw : |(2564897739/5000000000 : ℝ)|=(2564897739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_box_6 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5377842509/10000000000 : ℝ)*x 0 + (5129795669/10000000000 : ℝ)*x 1 + (-1212677479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377842509/10000000000 : ℝ)^6031 ≤ (47371130205047/100000000000000 : ℝ)^5007 := by
    have hnat : (5377842509 : ℕ)^6031*100000000000000^5007 ≤ 47371130205047^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377842509 10000000000 47371130205047 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5129795669/10000000000 : ℝ)^6031 ≤ (11187977202857/25000000000000 : ℝ)^5007 := by
    have hnat : (5129795669 : ℕ)^6031*25000000000000^5007 ≤ 11187977202857^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129795669 10000000000 11187977202857 25000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1212677479/10000000000 : ℝ)^6031 ≤ (3938480483891/50000000000000 : ℝ)^5007 := by
    have hnat : (1212677479 : ℕ)^6031*50000000000000^5007 ≤ 3938480483891^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1212677479 10000000000 3938480483891 50000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377842509/10000000000 : ℝ), (5129795669/10000000000 : ℝ), (-1212677479/10000000000 : ℝ)] ![(47371130205047/100000000000000 : ℝ), (11187977202857/25000000000000 : ℝ), (3938480483891/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377842509/10000000000 : ℝ)|^6031 ≤ (47371130205047/100000000000000 : ℝ)^5007
        have hw : |(5377842509/10000000000 : ℝ)|=(5377842509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5129795669/10000000000 : ℝ)|^6031 ≤ (11187977202857/25000000000000 : ℝ)^5007
        have hw : |(5129795669/10000000000 : ℝ)|=(5129795669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1212677479/10000000000 : ℝ)|^6031 ≤ (3938480483891/50000000000000 : ℝ)^5007
        have hw : |(-1212677479/10000000000 : ℝ)|=(1212677479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_box_7 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42821409/125000000 : ℝ)*x 0 + (2152872519/5000000000 : ℝ)*x 1 + (4305744371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42821409/125000000 : ℝ)^6031 ≤ (1719812732461/6250000000000 : ℝ)^5007 := by
    have hnat : (42821409 : ℕ)^6031*6250000000000^5007 ≤ 1719812732461^5007*125000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42821409 125000000 1719812732461 6250000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2152872519/5000000000 : ℝ)^6031 ≤ (36241501518307/100000000000000 : ℝ)^5007 := by
    have hnat : (2152872519 : ℕ)^6031*100000000000000^5007 ≤ 36241501518307^5007*5000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152872519 5000000000 36241501518307 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4305744371/10000000000 : ℝ)^6031 ≤ (4530186844499/12500000000000 : ℝ)^5007 := by
    have hnat : (4305744371 : ℕ)^6031*12500000000000^5007 ≤ 4530186844499^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4305744371 10000000000 4530186844499 12500000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42821409/125000000 : ℝ), (2152872519/5000000000 : ℝ), (4305744371/10000000000 : ℝ)] ![(1719812732461/6250000000000 : ℝ), (36241501518307/100000000000000 : ℝ), (4530186844499/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42821409/125000000 : ℝ)|^6031 ≤ (1719812732461/6250000000000 : ℝ)^5007
        have hw : |(42821409/125000000 : ℝ)|=(42821409/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2152872519/5000000000 : ℝ)|^6031 ≤ (36241501518307/100000000000000 : ℝ)^5007
        have hw : |(2152872519/5000000000 : ℝ)|=(2152872519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4305744371/10000000000 : ℝ)|^6031 ≤ (4530186844499/12500000000000 : ℝ)^5007
        have hw : |(4305744371/10000000000 : ℝ)|=(4305744371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_box_8 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1372887851/10000000000 : ℝ)*x 0 + (983198071/2000000000 : ℝ)*x 1 + (5468839997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1372887851/10000000000 : ℝ)^6031 ≤ (9146809499599/100000000000000 : ℝ)^5007 := by
    have hnat : (1372887851 : ℕ)^6031*100000000000000^5007 ≤ 9146809499599^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372887851 10000000000 9146809499599 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (983198071/2000000000 : ℝ)^6031 ≤ (42514909324273/100000000000000 : ℝ)^5007 := by
    have hnat : (983198071 : ℕ)^6031*100000000000000^5007 ≤ 42514909324273^5007*2000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983198071 2000000000 42514909324273 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5468839997/10000000000 : ℝ)^6031 ≤ (12084570289569/25000000000000 : ℝ)^5007 := by
    have hnat : (5468839997 : ℕ)^6031*25000000000000^5007 ≤ 12084570289569^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468839997 10000000000 12084570289569 25000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1372887851/10000000000 : ℝ), (983198071/2000000000 : ℝ), (5468839997/10000000000 : ℝ)] ![(9146809499599/100000000000000 : ℝ), (42514909324273/100000000000000 : ℝ), (12084570289569/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1372887851/10000000000 : ℝ)|^6031 ≤ (9146809499599/100000000000000 : ℝ)^5007
        have hw : |(-1372887851/10000000000 : ℝ)|=(1372887851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(983198071/2000000000 : ℝ)|^6031 ≤ (42514909324273/100000000000000 : ℝ)^5007
        have hw : |(983198071/2000000000 : ℝ)|=(983198071/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5468839997/10000000000 : ℝ)|^6031 ≤ (12084570289569/25000000000000 : ℝ)^5007
        have hw : |(5468839997/10000000000 : ℝ)|=(5468839997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_box_9 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5152447641/10000000000 : ℝ)*x 0 + (-528247591/5000000000 : ℝ)*x 1 + (2734419813/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5152447641/10000000000 : ℝ)^6031 ≤ (8998008965053/20000000000000 : ℝ)^5007 := by
    have hnat : (5152447641 : ℕ)^6031*20000000000000^5007 ≤ 8998008965053^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152447641 10000000000 8998008965053 20000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528247591/5000000000 : ℝ)^6031 ≤ (6671677955149/100000000000000 : ℝ)^5007 := by
    have hnat : (528247591 : ℕ)^6031*100000000000000^5007 ≤ 6671677955149^5007*5000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528247591 5000000000 6671677955149 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2734419813/5000000000 : ℝ)^6031 ≤ (1510571162763/3125000000000 : ℝ)^5007 := by
    have hnat : (2734419813 : ℕ)^6031*3125000000000^5007 ≤ 1510571162763^5007*5000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734419813 5000000000 1510571162763 3125000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5152447641/10000000000 : ℝ), (-528247591/5000000000 : ℝ), (2734419813/5000000000 : ℝ)] ![(8998008965053/20000000000000 : ℝ), (6671677955149/100000000000000 : ℝ), (1510571162763/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5152447641/10000000000 : ℝ)|^6031 ≤ (8998008965053/20000000000000 : ℝ)^5007
        have hw : |(5152447641/10000000000 : ℝ)|=(5152447641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-528247591/5000000000 : ℝ)|^6031 ≤ (6671677955149/100000000000000 : ℝ)^5007
        have hw : |(-528247591/5000000000 : ℝ)|=(528247591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2734419813/5000000000 : ℝ)|^6031 ≤ (1510571162763/3125000000000 : ℝ)^5007
        have hw : |(2734419813/5000000000 : ℝ)|=(2734419813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_box_10 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5152447379/10000000000 : ℝ)*x 0 + (1367209939/2500000000 : ℝ)*x 1 + (-1056495361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5152447379/10000000000 : ℝ)^6031 ≤ (44990042069667/100000000000000 : ℝ)^5007 := by
    have hnat : (5152447379 : ℕ)^6031*100000000000000^5007 ≤ 44990042069667^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152447379 10000000000 44990042069667 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1367209939/2500000000 : ℝ)^6031 ≤ (3021142412029/6250000000000 : ℝ)^5007 := by
    have hnat : (1367209939 : ℕ)^6031*6250000000000^5007 ≤ 3021142412029^5007*2500000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367209939 2500000000 3021142412029 6250000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056495361/10000000000 : ℝ)^6031 ≤ (1334335863339/20000000000000 : ℝ)^5007 := by
    have hnat : (1056495361 : ℕ)^6031*20000000000000^5007 ≤ 1334335863339^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056495361 10000000000 1334335863339 20000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5152447379/10000000000 : ℝ), (1367209939/2500000000 : ℝ), (-1056495361/10000000000 : ℝ)] ![(44990042069667/100000000000000 : ℝ), (3021142412029/6250000000000 : ℝ), (1334335863339/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5152447379/10000000000 : ℝ)|^6031 ≤ (44990042069667/100000000000000 : ℝ)^5007
        have hw : |(5152447379/10000000000 : ℝ)|=(5152447379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1367209939/2500000000 : ℝ)|^6031 ≤ (3021142412029/6250000000000 : ℝ)^5007
        have hw : |(1367209939/2500000000 : ℝ)|=(1367209939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1056495361/10000000000 : ℝ)|^6031 ≤ (1334335863339/20000000000000 : ℝ)^5007
        have hw : |(-1056495361/10000000000 : ℝ)|=(1056495361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_box_11 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4737649399/10000000000 : ℝ)*x 0 + (3646594857/10000000000 : ℝ)*x 1 + (3646595787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4737649399/10000000000 : ℝ)^6031 ≤ (40664093628809/100000000000000 : ℝ)^5007 := by
    have hnat : (4737649399 : ℕ)^6031*100000000000000^5007 ≤ 40664093628809^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4737649399 10000000000 40664093628809 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3646594857/10000000000 : ℝ)^6031 ≤ (3708493577541/12500000000000 : ℝ)^5007 := by
    have hnat : (3646594857 : ℕ)^6031*12500000000000^5007 ≤ 3708493577541^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3646594857 10000000000 3708493577541 12500000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3646595787/10000000000 : ℝ)^6031 ≤ (7416989433507/25000000000000 : ℝ)^5007 := by
    have hnat : (3646595787 : ℕ)^6031*25000000000000^5007 ≤ 7416989433507^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3646595787 10000000000 7416989433507 25000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4737649399/10000000000 : ℝ), (3646594857/10000000000 : ℝ), (3646595787/10000000000 : ℝ)] ![(40664093628809/100000000000000 : ℝ), (3708493577541/12500000000000 : ℝ), (7416989433507/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4737649399/10000000000 : ℝ)|^6031 ≤ (40664093628809/100000000000000 : ℝ)^5007
        have hw : |(4737649399/10000000000 : ℝ)|=(4737649399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3646594857/10000000000 : ℝ)|^6031 ≤ (3708493577541/12500000000000 : ℝ)^5007
        have hw : |(3646594857/10000000000 : ℝ)|=(3646594857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3646595787/10000000000 : ℝ)|^6031 ≤ (7416989433507/25000000000000 : ℝ)^5007
        have hw : |(3646595787/10000000000 : ℝ)|=(3646595787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_box_12 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-232058763/2500000000 : ℝ)*x 0 + (2805222979/5000000000 : ℝ)*x 1 + (204009679/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (232058763/2500000000 : ℝ)^6031 ≤ (5708603698923/100000000000000 : ℝ)^5007 := by
    have hnat : (232058763 : ℕ)^6031*100000000000000^5007 ≤ 5708603698923^5007*2500000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      232058763 2500000000 5708603698923 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2805222979/5000000000 : ℝ)^6031 ≤ (24924928361577/50000000000000 : ℝ)^5007 := by
    have hnat : (2805222979 : ℕ)^6031*50000000000000^5007 ≤ 24924928361577^5007*5000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2805222979 5000000000 24924928361577 50000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (204009679/400000000 : ℝ)^6031 ≤ (44441539560771/100000000000000 : ℝ)^5007 := by
    have hnat : (204009679 : ℕ)^6031*100000000000000^5007 ≤ 44441539560771^5007*400000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204009679 400000000 44441539560771 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-232058763/2500000000 : ℝ), (2805222979/5000000000 : ℝ), (204009679/400000000 : ℝ)] ![(5708603698923/100000000000000 : ℝ), (24924928361577/50000000000000 : ℝ), (44441539560771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-232058763/2500000000 : ℝ)|^6031 ≤ (5708603698923/100000000000000 : ℝ)^5007
        have hw : |(-232058763/2500000000 : ℝ)|=(232058763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2805222979/5000000000 : ℝ)|^6031 ≤ (24924928361577/50000000000000 : ℝ)^5007
        have hw : |(2805222979/5000000000 : ℝ)|=(2805222979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(204009679/400000000 : ℝ)|^6031 ≤ (44441539560771/100000000000000 : ℝ)^5007
        have hw : |(204009679/400000000 : ℝ)|=(204009679/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_box_13 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5397572501/10000000000 : ℝ)*x 0 + (-306391787/2500000000 : ℝ)*x 1 + (79691277/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5397572501/10000000000 : ℝ)^6031 ≤ (47580544851141/100000000000000 : ℝ)^5007 := by
    have hnat : (5397572501 : ℕ)^6031*100000000000000^5007 ≤ 47580544851141^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397572501 10000000000 47580544851141 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (306391787/2500000000 : ℝ)^6031 ≤ (319116727093/4000000000000 : ℝ)^5007 := by
    have hnat : (306391787 : ℕ)^6031*4000000000000^5007 ≤ 319116727093^5007*2500000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      306391787 2500000000 319116727093 4000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (79691277/156250000 : ℝ)^6031 ≤ (22220768484171/50000000000000 : ℝ)^5007 := by
    have hnat : (79691277 : ℕ)^6031*50000000000000^5007 ≤ 22220768484171^5007*156250000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79691277 156250000 22220768484171 50000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5397572501/10000000000 : ℝ), (-306391787/2500000000 : ℝ), (79691277/156250000 : ℝ)] ![(47580544851141/100000000000000 : ℝ), (319116727093/4000000000000 : ℝ), (22220768484171/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5397572501/10000000000 : ℝ)|^6031 ≤ (47580544851141/100000000000000 : ℝ)^5007
        have hw : |(5397572501/10000000000 : ℝ)|=(5397572501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-306391787/2500000000 : ℝ)|^6031 ≤ (319116727093/4000000000000 : ℝ)^5007
        have hw : |(-306391787/2500000000 : ℝ)|=(306391787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(79691277/156250000 : ℝ)|^6031 ≤ (22220768484171/50000000000000 : ℝ)^5007
        have hw : |(79691277/156250000 : ℝ)|=(79691277/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_box_14 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5397572527/10000000000 : ℝ)*x 0 + (1275060251/2500000000 : ℝ)*x 1 + (-15319601/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5397572527/10000000000 : ℝ)^6031 ≤ (47580545127209/100000000000000 : ℝ)^5007 := by
    have hnat : (5397572527 : ℕ)^6031*100000000000000^5007 ≤ 47580545127209^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397572527 10000000000 47580545127209 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1275060251/2500000000 : ℝ)^6031 ≤ (44441529369479/100000000000000 : ℝ)^5007 := by
    have hnat : (1275060251 : ℕ)^6031*100000000000000^5007 ≤ 44441529369479^5007*2500000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1275060251 2500000000 44441529369479 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15319601/125000000 : ℝ)^6031 ≤ (997240685627/12500000000000 : ℝ)^5007 := by
    have hnat : (15319601 : ℕ)^6031*12500000000000^5007 ≤ 997240685627^5007*125000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15319601 125000000 997240685627 12500000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5397572527/10000000000 : ℝ), (1275060251/2500000000 : ℝ), (-15319601/125000000 : ℝ)] ![(47580545127209/100000000000000 : ℝ), (44441529369479/100000000000000 : ℝ), (997240685627/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5397572527/10000000000 : ℝ)|^6031 ≤ (47580545127209/100000000000000 : ℝ)^5007
        have hw : |(5397572527/10000000000 : ℝ)|=(5397572527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1275060251/2500000000 : ℝ)|^6031 ≤ (44441529369479/100000000000000 : ℝ)^5007
        have hw : |(1275060251/2500000000 : ℝ)|=(1275060251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-15319601/125000000 : ℝ)|^6031 ≤ (997240685627/12500000000000 : ℝ)^5007
        have hw : |(-15319601/125000000 : ℝ)|=(15319601/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_box_15 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (826316581/2500000000 : ℝ)*x 0 + (109073209/250000000 : ℝ)*x 1 + (4362933047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (826316581/2500000000 : ℝ)^6031 ≤ (13177942440971/50000000000000 : ℝ)^5007 := by
    have hnat : (826316581 : ℕ)^6031*50000000000000^5007 ≤ 13177942440971^5007*2500000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      826316581 2500000000 13177942440971 50000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109073209/250000000 : ℝ)^6031 ≤ (36822033726981/100000000000000 : ℝ)^5007 := by
    have hnat : (109073209 : ℕ)^6031*100000000000000^5007 ≤ 36822033726981^5007*250000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109073209 250000000 36822033726981 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4362933047/10000000000 : ℝ)^6031 ≤ (9205520343519/25000000000000 : ℝ)^5007 := by
    have hnat : (4362933047 : ℕ)^6031*25000000000000^5007 ≤ 9205520343519^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362933047 10000000000 9205520343519 25000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(826316581/2500000000 : ℝ), (109073209/250000000 : ℝ), (4362933047/10000000000 : ℝ)] ![(13177942440971/50000000000000 : ℝ), (36822033726981/100000000000000 : ℝ), (9205520343519/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(826316581/2500000000 : ℝ)|^6031 ≤ (13177942440971/50000000000000 : ℝ)^5007
        have hw : |(826316581/2500000000 : ℝ)|=(826316581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(109073209/250000000 : ℝ)|^6031 ≤ (36822033726981/100000000000000 : ℝ)^5007
        have hw : |(109073209/250000000 : ℝ)|=(109073209/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4362933047/10000000000 : ℝ)|^6031 ≤ (9205520343519/25000000000000 : ℝ)^5007
        have hw : |(4362933047/10000000000 : ℝ)|=(4362933047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1766_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11252043/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17667/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1843/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(69231/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58891/100000 : ℝ) ∧ (82447/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (93187/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17667/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1843/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17667/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1843/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17667/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1843/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17667/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1843/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17667/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1843/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17667/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1843/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1843/20000 : ℝ) ^ (6015/1024 : ℝ) ≤ (82683976506033/100000000000000000000 : ℝ) := by
    have hpowers : (1843/20000 : ℝ)^6015 ≤ (82683976506033/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1843 : ℕ)^6015*100000000000000000000^1024 ≤ 82683976506033^1024*20000^6015 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1843 20000 82683976506033 100000000000000000000 6015 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1843/20000 : ℝ)) (X := (82683976506033/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6015 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17667/100000 : ℝ) ^ (6015/1024 : ℝ) ≤ (756565775439149/20000000000000000000 : ℝ) := by
    have hpowers : (17667/100000 : ℝ)^6015 ≤ (756565775439149/20000000000000000000 : ℝ)^1024 := by
      have hnat : (17667 : ℕ)^6015*20000000000000000000^1024 ≤ 756565775439149^1024*100000^6015 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17667 100000 756565775439149 20000000000000000000 6015 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17667/100000 : ℝ)) (X := (756565775439149/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6015 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000082683976506033/50000000000000000000 : ℝ) ≤ (625000175952481/625000000000000 : ℝ) ^ (6015/1024 : ℝ) := by
    have hpowers : (50000082683976506033/50000000000000000000 : ℝ)^1024 ≤ (625000175952481/625000000000000 : ℝ)^6015 := by
      have hnat : (50000082683976506033 : ℕ)^1024*625000000000000^6015 ≤ 625000175952481^6015*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000082683976506033 50000000000000000000 625000175952481 625000000000000 1024 6015 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625000175952481/625000000000000 : ℝ)) (X := (50000082683976506033/50000000000000000000 : ℝ)) (by norm_num) 6015 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50001932756426850889/50000000000000000000 : ℝ) ≤ (500003290292339/500000000000000 : ℝ) ^ (6015/1024 : ℝ) := by
    have hpowers : (50001932756426850889/50000000000000000000 : ℝ)^1024 ≤ (500003290292339/500000000000000 : ℝ)^6015 := by
      have hnat : (50001932756426850889 : ℕ)^1024*500000000000000^6015 ≤ 500003290292339^6015*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001932756426850889 50000000000000000000 500003290292339 500000000000000 1024 6015 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500003290292339/500000000000000 : ℝ)) (X := (50001932756426850889/50000000000000000000 : ℝ)) (by norm_num) 6015 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10000756565775439149/10000000000000000000 : ℝ) ≤ (1250016099556733/1250000000000000 : ℝ) ^ (6015/1024 : ℝ) := by
    have hpowers : (10000756565775439149/10000000000000000000 : ℝ)^1024 ≤ (1250016099556733/1250000000000000 : ℝ)^6015 := by
      have hnat : (10000756565775439149 : ℕ)^1024*1250000000000000^6015 ≤ 1250016099556733^6015*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000756565775439149 10000000000000000000 1250016099556733 1250000000000000 1024 6015 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250016099556733/1250000000000000 : ℝ)) (X := (10000756565775439149/10000000000000000000 : ℝ)) (by norm_num) 6015 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(82683976506033/100000000000000000000 : ℝ) ≤ ((10564857859689669059/10565000000000000000 : ℝ)+2*(15747651771/211300000000000 : ℝ)*(1843/20000 : ℝ))^(6015/1024 : ℝ) := by
    rw [show (10564857859689669059/10565000000000000000 : ℝ)+2*(15747651771/211300000000000 : ℝ)*(1843/20000 : ℝ)=(625000175952481/625000000000000 : ℝ) by norm_num, show 1+2*(82683976506033/100000000000000000000 : ℝ)=(50000082683976506033/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(756565775439149/20000000000000000000 : ℝ)+(82683976506033/100000000000000000000 : ℝ) ≤ ((10564857859689669059/10565000000000000000 : ℝ)+(15747651771/211300000000000 : ℝ)*((17667/100000 : ℝ)+(1843/20000 : ℝ)))^(6015/1024 : ℝ) := by
    rw [show (10564857859689669059/10565000000000000000 : ℝ)+(15747651771/211300000000000 : ℝ)*((17667/100000 : ℝ)+(1843/20000 : ℝ))=(500003290292339/500000000000000 : ℝ) by norm_num, show 1+(756565775439149/20000000000000000000 : ℝ)+(82683976506033/100000000000000000000 : ℝ)=(50001932756426850889/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(756565775439149/20000000000000000000 : ℝ) ≤ ((10564857859689669059/10565000000000000000 : ℝ)+2*(15747651771/211300000000000 : ℝ)*(17667/100000 : ℝ))^(6015/1024 : ℝ) := by
    rw [show (10564857859689669059/10565000000000000000 : ℝ)+2*(15747651771/211300000000000 : ℝ)*(17667/100000 : ℝ)=(1250016099556733/1250000000000000 : ℝ) by norm_num, show 1+2*(756565775439149/20000000000000000000 : ℝ)=(10000756565775439149/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10564857859689669059/10565000000000000000 : ℝ)*(X 1 0+X 2 0)+(15747651771/211300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6015/1024 : ℝ)) (lo := (1843/20000 : ℝ)) (hi := (17667/100000 : ℝ)) (c := (10564857859689669059/10565000000000000000 : ℝ)) (alpha := (15747651771/211300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10564857859689669059/10565000000000000000 : ℝ)*(X 0 1+X 2 1)+(15747651771/211300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6015/1024 : ℝ)) (lo := (1843/20000 : ℝ)) (hi := (17667/100000 : ℝ)) (c := (10564857859689669059/10565000000000000000 : ℝ)) (alpha := (15747651771/211300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10564857859689669059/10565000000000000000 : ℝ)*(X 0 2+X 1 2)+(15747651771/211300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6015/1024 : ℝ)) (lo := (1843/20000 : ℝ)) (hi := (17667/100000 : ℝ)) (c := (10564857859689669059/10565000000000000000 : ℝ)) (alpha := (15747651771/211300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-388299039/5000000000 : ℝ)*X 0 0+(540858671/1000000000 : ℝ)*X 0 1+(1081717331/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1298109587/2500000000 : ℝ)*X 1 0+(-135664339/1250000000 : ℝ)*X 1 1+(1352146717/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2596219043/5000000000 : ℝ)*X 2 0+(5408586991/10000000000 : ℝ)*X 2 1+(-542657451/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((451307081/1000000000 : ℝ)*X 0 0+(3764094461/10000000000 : ℝ)*X 0 1+(1882046641/5000000000 : ℝ)*X 0 2+(451307081/1000000000 : ℝ)*X 1 0+(3764094461/10000000000 : ℝ)*X 1 1+(1882046641/5000000000 : ℝ)*X 1 2+(451307081/1000000000 : ℝ)*X 2 0+(3764094461/10000000000 : ℝ)*X 2 1+(1882046641/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-61561591/400000000 : ℝ)*X 0 0+(2564897951/5000000000 : ℝ)*X 0 1+(5129795551/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1075568567/2000000000 : ℝ)*X 1 0+(-606338647/5000000000 : ℝ)*X 1 1+(2564897739/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5377842509/10000000000 : ℝ)*X 2 0+(5129795669/10000000000 : ℝ)*X 2 1+(-1212677479/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((42821409/125000000 : ℝ)*X 0 0+(2152872519/5000000000 : ℝ)*X 0 1+(4305744371/10000000000 : ℝ)*X 0 2+(42821409/125000000 : ℝ)*X 1 0+(2152872519/5000000000 : ℝ)*X 1 1+(4305744371/10000000000 : ℝ)*X 1 2+(42821409/125000000 : ℝ)*X 2 0+(2152872519/5000000000 : ℝ)*X 2 1+(4305744371/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1372887851/10000000000 : ℝ)*X 0 0+(983198071/2000000000 : ℝ)*X 0 1+(5468839997/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5152447641/10000000000 : ℝ)*X 1 0+(-528247591/5000000000 : ℝ)*X 1 1+(2734419813/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5152447379/10000000000 : ℝ)*X 2 0+(1367209939/2500000000 : ℝ)*X 2 1+(-1056495361/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4737649399/10000000000 : ℝ)*X 0 0+(3646594857/10000000000 : ℝ)*X 0 1+(3646595787/10000000000 : ℝ)*X 0 2+(4737649399/10000000000 : ℝ)*X 1 0+(3646594857/10000000000 : ℝ)*X 1 1+(3646595787/10000000000 : ℝ)*X 1 2+(4737649399/10000000000 : ℝ)*X 2 0+(3646594857/10000000000 : ℝ)*X 2 1+(3646595787/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-232058763/2500000000 : ℝ)*X 0 0+(2805222979/5000000000 : ℝ)*X 0 1+(204009679/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5397572501/10000000000 : ℝ)*X 1 0+(-306391787/2500000000 : ℝ)*X 1 1+(79691277/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5397572527/10000000000 : ℝ)*X 2 0+(1275060251/2500000000 : ℝ)*X 2 1+(-15319601/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((826316581/2500000000 : ℝ)*X 0 0+(109073209/250000000 : ℝ)*X 0 1+(4362933047/10000000000 : ℝ)*X 0 2+(826316581/2500000000 : ℝ)*X 1 0+(109073209/250000000 : ℝ)*X 1 1+(4362933047/10000000000 : ℝ)*X 1 2+(826316581/2500000000 : ℝ)*X 2 0+(109073209/250000000 : ℝ)*X 2 1+(4362933047/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-69231/100000 : ℝ) ≤ (-45712169216779831355534576091177/66031250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5758899/100000000000000 : ℝ)*(upper1) + (8000611/20000000000000 : ℝ)*(upper3) + (25456637/100000000000000 : ℝ)*(lower4) + (8134333/20000000000000 : ℝ)*(lower5) + (138033760900583/12500000000000 : ℝ)*(major0) + (138033760900583/12500000000000 : ℝ)*(major1) + (138033760900583/12500000000000 : ℝ)*(major2) + (842078769/50000000000000 : ℝ)*(sp1) + (49125453/25000000000000 : ℝ)*(sp3) + (870459303834249/50000000000000 : ℝ)*(sp4) + (1740916923510959/100000000000000 : ℝ)*(sp5) + (870459285518759/50000000000000 : ℝ)*(sp6) + (245348699119639/50000000000000 : ℝ)*(sp7) + (1831549/5000000000000 : ℝ)*(sp14) + (49069759474109/10000000000000 : ℝ)*(f.failure) + (870459303834249/50000000000000 : ℝ)*(f.sum) + (1736422879747/5282500000000000000000000000 : ℝ)*base65 + (1424042965767438603/132062500000000000000000000000000 : ℝ)*base68 + (1419899165165188603/132062500000000000000000000000000 : ℝ)*base70 + (191049196755001103/132062500000000000000000000000000 : ℝ)*base72 + (6680110225083/5282500000000000000000000000 : ℝ)*base74 + (1090852502705438603/132062500000000000000000000000000 : ℝ)*base76 + (657592086756813603/132062500000000000000000000000000 : ℝ)*base78 + (1169257196771063603/132062500000000000000000000000000 : ℝ)*base80 + (4556324419257/1320625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (145313/50000000000000000000 : ℝ)*base90 + (145313/50000000000000000000 : ℝ)*base92 + (145313/50000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58891/100000 : ℝ) ≤ (311105967189009827223437685481827/528250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (38255961/100000000000000 : ℝ)*(lower0) + (13187797/100000000000000 : ℝ)*(upper1) + (36335403/100000000000000 : ℝ)*(upper2) + (26884819/50000000000000 : ℝ)*(upper3) + (2570911/50000000000000 : ℝ)*(lower5) + (1237359939861817/100000000000000 : ℝ)*(major0) + (1237359939861817/100000000000000 : ℝ)*(major1) + (1237359939861817/100000000000000 : ℝ)*(major2) + (1905250746096481/100000000000000 : ℝ)*(sp0) + (1905250746096481/100000000000000 : ℝ)*(sp1) + (1905250013526771/100000000000000 : ℝ)*(sp2) + (274917456201023/50000000000000 : ℝ)*(sp3) + (73256971/10000000000000 : ℝ)*(sp6) + (1494042461/50000000000000 : ℝ)*(sp11) + (68729737560871/12500000000000 : ℝ)*(f.failure) + (1905250746096481/100000000000000 : ℝ)*(f.sum) + (10914177097393/10565000000000000000000000000 : ℝ)*base66 + (12093888123839229797/1056500000000000000000000000000000 : ℝ)*base68 + (2658665665400729797/1056500000000000000000000000000000 : ℝ)*base70 + (7907202238403229797/1056500000000000000000000000000000 : ℝ)*base72 + (16021396013813/10565000000000000000000000000 : ℝ)*base74 + (1516114218995229797/1056500000000000000000000000000000 : ℝ)*base76 + (6758310582305229797/1056500000000000000000000000000000 : ℝ)*base78 + (3372538246405729797/1056500000000000000000000000000000 : ℝ)*base80 + (96592088817397/10565000000000000000000000000 : ℝ)*base81 + (15547/62500000000000000000 : ℝ)*base90 + (15547/62500000000000000000 : ℝ)*base92 + (15547/62500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (82447/100000 : ℝ) ≤ (435540809732312432961570835647633/528250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35388893/100000000000000 : ℝ)*(upper0) + (23695423/50000000000000 : ℝ)*(upper2) + (6532983/50000000000000 : ℝ)*(lower3) + (32051167/100000000000000 : ℝ)*(lower5) + (1180413575087843/100000000000000 : ℝ)*(major0) + (1180413575087843/100000000000000 : ℝ)*(major1) + (1180413575087843/100000000000000 : ℝ)*(major2) + (382491851/50000000000000 : ℝ)*(sp3) + (756476677/100000000000000 : ℝ)*(sp4) + (452202343165547/25000000000000 : ℝ)*(sp8) + (1808810899435903/100000000000000 : ℝ)*(sp9) + (1808810899435903/100000000000000 : ℝ)*(sp10) + (262266117709011/50000000000000 : ℝ)*(sp11) + (770297039/100000000000000 : ℝ)*(sp12) + (131133250100431/25000000000000 : ℝ)*(f.failure) + (1808810899435903/100000000000000 : ℝ)*(f.sum) + (13263688399751/5282500000000000000000000000 : ℝ)*base66 + (1454362693586200263/1056500000000000000000000000000000 : ℝ)*base68 + (11682542605757200263/1056500000000000000000000000000000 : ℝ)*base70 + (3829461314964700263/1056500000000000000000000000000000 : ℝ)*base72 + (59374763726503/10565000000000000000000000000 : ℝ)*base73 + (2843528473392200263/1056500000000000000000000000000000 : ℝ)*base76 + (8422905056855700263/1056500000000000000000000000000000 : ℝ)*base78 + (2372320586114200263/1056500000000000000000000000000000 : ℝ)*base80 + (2134129600861/5282500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (180533/125000000000000000000 : ℝ)*base89 + (180533/125000000000000000000 : ℝ)*base91 + (180533/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-93187/100000 : ℝ) ≤ (-49224614731592096119186635961491/52825000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (372011/50000000000000 : ℝ)*(upper3) + (248855593/100000000000000 : ℝ)*(lower4) + (121113449/50000000000000 : ℝ)*(upper5) + (247994269939517/20000000000000 : ℝ)*(major0) + (247994269939517/20000000000000 : ℝ)*(major1) + (247994269939517/20000000000000 : ℝ)*(major2) + (343816583/6250000000000 : ℝ)*(sp4) + (11066917179/50000000000000 : ℝ)*(sp5) + (75423378647/50000000000000 : ℝ)*(sp6) + (16658812949/50000000000000 : ℝ)*(sp7) + (980000160262037/50000000000000 : ℝ)*(sp12) + (391996737551009/20000000000000 : ℝ)*(sp13) + (1959854974832109/100000000000000 : ℝ)*(sp14) + (68870624840403/12500000000000 : ℝ)*(sp15) + (275499158174561/50000000000000 : ℝ)*(f.failure) + (980002910794701/50000000000000 : ℝ)*(f.sum) + (7804700664663/2113000000000000000000000000 : ℝ)*base65 + (461096523721054503/211300000000000000000000000000000 : ℝ)*base67 + (1230034585266545497/211300000000000000000000000000000 : ℝ)*base70 + (560912575597645497/211300000000000000000000000000000 : ℝ)*base72 + (10329250173331/2113000000000000000000000000 : ℝ)*base73 + (1668141682234345497/211300000000000000000000000000000 : ℝ)*base76 + (1383236733435845497/211300000000000000000000000000000 : ℝ)*base78 + (1265071996705145497/211300000000000000000000000000000 : ℝ)*base80 + (5568841994213/2113000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (621877/250000000000000000000 : ℝ)*base90 + (621877/250000000000000000000 : ℝ)*base92 + (621877/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1766_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11252043/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17667/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1843/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(69231/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58891/100000 : ℝ) else (82447/100000 : ℝ) ≤ X j i ∧ X j i ≤ (93187/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1766_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1766_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11252043/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4417/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4607/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(69231/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58891/100000 : ℝ) else (82447/100000 : ℝ) ≤ X j i ∧ X j i ≤ (93187/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1766_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1766_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11252043/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4417/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4607/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(69231/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58891/100000 : ℝ) else (82447/100000 : ℝ) ≤ X j i ∧ X j i ≤ (93187/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1766_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
