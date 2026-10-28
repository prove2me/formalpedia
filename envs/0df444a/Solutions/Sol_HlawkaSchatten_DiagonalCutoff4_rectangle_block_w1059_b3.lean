-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1059_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:02:21.765605+00:00
-- url     : https://prove2.me/submissions/4a8a7f42-8319-489e-b322-261c6e46ba3d

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
theorem support_rectangle_w1059_s9_0 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344989541/10000000000 : ℝ)*x 0 + (-2273232593/10000000000 : ℝ)*x 1 + (2632174183/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344989541/10000000000 : ℝ)^2063 ≤ (43464982047697/100000000000000 : ℝ)^1551 := by
    have hnat : (5344989541 : ℕ)^2063*100000000000000^1551 ≤ 43464982047697^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344989541 10000000000 43464982047697 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2273232593/10000000000 : ℝ)^2063 ≤ (13940098310181/100000000000000 : ℝ)^1551 := by
    have hnat : (2273232593 : ℕ)^2063*100000000000000^1551 ≤ 13940098310181^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273232593 10000000000 13940098310181 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632174183/5000000000 : ℝ)^2063 ≤ (8518983926827/20000000000000 : ℝ)^1551 := by
    have hnat : (2632174183 : ℕ)^2063*20000000000000^1551 ≤ 8518983926827^1551*5000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632174183 5000000000 8518983926827 20000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344989541/10000000000 : ℝ), (-2273232593/10000000000 : ℝ), (2632174183/5000000000 : ℝ)] ![(43464982047697/100000000000000 : ℝ), (13940098310181/100000000000000 : ℝ), (8518983926827/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344989541/10000000000 : ℝ)|^2063 ≤ (43464982047697/100000000000000 : ℝ)^1551
        have hw : |(5344989541/10000000000 : ℝ)|=(5344989541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2273232593/10000000000 : ℝ)|^2063 ≤ (13940098310181/100000000000000 : ℝ)^1551
        have hw : |(-2273232593/10000000000 : ℝ)|=(2273232593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632174183/5000000000 : ℝ)|^2063 ≤ (8518983926827/20000000000000 : ℝ)^1551
        have hw : |(2632174183/5000000000 : ℝ)|=(2632174183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s9_1 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1103611997/5000000000 : ℝ)*x 0 + (5264674339/10000000000 : ℝ)*x 1 + (2697063889/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1103611997/5000000000 : ℝ)^2063 ≤ (13404289672681/100000000000000 : ℝ)^1551 := by
    have hnat : (1103611997 : ℕ)^2063*100000000000000^1551 ≤ 13404289672681^1551*5000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103611997 5000000000 13404289672681 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264674339/10000000000 : ℝ)^2063 ≤ (42598427853007/100000000000000 : ℝ)^1551 := by
    have hnat : (5264674339 : ℕ)^2063*100000000000000^1551 ≤ 42598427853007^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264674339 10000000000 42598427853007 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697063889/5000000000 : ℝ)^2063 ≤ (43997282457139/100000000000000 : ℝ)^1551 := by
    have hnat : (2697063889 : ℕ)^2063*100000000000000^1551 ≤ 43997282457139^1551*5000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697063889 5000000000 43997282457139 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1103611997/5000000000 : ℝ), (5264674339/10000000000 : ℝ), (2697063889/5000000000 : ℝ)] ![(13404289672681/100000000000000 : ℝ), (42598427853007/100000000000000 : ℝ), (43997282457139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1103611997/5000000000 : ℝ)|^2063 ≤ (13404289672681/100000000000000 : ℝ)^1551
        have hw : |(-1103611997/5000000000 : ℝ)|=(1103611997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264674339/10000000000 : ℝ)|^2063 ≤ (42598427853007/100000000000000 : ℝ)^1551
        have hw : |(5264674339/10000000000 : ℝ)|=(5264674339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697063889/5000000000 : ℝ)|^2063 ≤ (43997282457139/100000000000000 : ℝ)^1551
        have hw : |(2697063889/5000000000 : ℝ)|=(2697063889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s9_2 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1328059223/2500000000 : ℝ)*x 0 + (-267931573/1250000000 : ℝ)*x 1 + (5394127863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328059223/2500000000 : ℝ)^2063 ≤ (43111077266189/100000000000000 : ℝ)^1551 := by
    have hnat : (1328059223 : ℕ)^2063*100000000000000^1551 ≤ 43111077266189^1551*2500000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328059223 2500000000 43111077266189 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (267931573/1250000000 : ℝ)^2063 ≤ (257832786783/2000000000000 : ℝ)^1551 := by
    have hnat : (267931573 : ℕ)^2063*2000000000000^1551 ≤ 257832786783^1551*1250000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267931573 1250000000 257832786783 2000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394127863/10000000000 : ℝ)^2063 ≤ (43997283379309/100000000000000 : ℝ)^1551 := by
    have hnat : (5394127863 : ℕ)^2063*100000000000000^1551 ≤ 43997283379309^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394127863 10000000000 43997283379309 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328059223/2500000000 : ℝ), (-267931573/1250000000 : ℝ), (5394127863/10000000000 : ℝ)] ![(43111077266189/100000000000000 : ℝ), (257832786783/2000000000000 : ℝ), (43997283379309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328059223/2500000000 : ℝ)|^2063 ≤ (43111077266189/100000000000000 : ℝ)^1551
        have hw : |(1328059223/2500000000 : ℝ)|=(1328059223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-267931573/1250000000 : ℝ)|^2063 ≤ (257832786783/2000000000000 : ℝ)^1551
        have hw : |(-267931573/1250000000 : ℝ)|=(267931573/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394127863/10000000000 : ℝ)|^2063 ≤ (43997283379309/100000000000000 : ℝ)^1551
        have hw : |(5394127863/10000000000 : ℝ)|=(5394127863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s9_3 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656118107/5000000000 : ℝ)*x 0 + (67426599/125000000 : ℝ)*x 1 + (-1071726711/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656118107/5000000000 : ℝ)^2063 ≤ (2155553497379/5000000000000 : ℝ)^1551 := by
    have hnat : (2656118107 : ℕ)^2063*5000000000000^1551 ≤ 2155553497379^1551*5000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656118107 5000000000 2155553497379 5000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67426599/125000000 : ℝ)^2063 ≤ (21998641998853/50000000000000 : ℝ)^1551 := by
    have hnat : (67426599 : ℕ)^2063*50000000000000^1551 ≤ 21998641998853^1551*125000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67426599 125000000 21998641998853 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1071726711/5000000000 : ℝ)^2063 ≤ (12891646043023/100000000000000 : ℝ)^1551 := by
    have hnat : (1071726711 : ℕ)^2063*100000000000000^1551 ≤ 12891646043023^1551*5000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071726711 5000000000 12891646043023 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656118107/5000000000 : ℝ), (67426599/125000000 : ℝ), (-1071726711/5000000000 : ℝ)] ![(2155553497379/5000000000000 : ℝ), (21998641998853/50000000000000 : ℝ), (12891646043023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656118107/5000000000 : ℝ)|^2063 ≤ (2155553497379/5000000000000 : ℝ)^1551
        have hw : |(2656118107/5000000000 : ℝ)|=(2656118107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67426599/125000000 : ℝ)|^2063 ≤ (21998641998853/50000000000000 : ℝ)^1551
        have hw : |(67426599/125000000 : ℝ)|=(67426599/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1071726711/5000000000 : ℝ)|^2063 ≤ (12891646043023/100000000000000 : ℝ)^1551
        have hw : |(-1071726711/5000000000 : ℝ)|=(1071726711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s9_4 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (218825527/500000000 : ℝ)*x 0 + (2252530413/5000000000 : ℝ)*x 1 + (4251702953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218825527/500000000 : ℝ)^2063 ≤ (3331661551233/10000000000000 : ℝ)^1551 := by
    have hnat : (218825527 : ℕ)^2063*10000000000000^1551 ≤ 3331661551233^1551*500000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218825527 500000000 3331661551233 10000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2252530413/5000000000 : ℝ)^2063 ≤ (34624532624401/100000000000000 : ℝ)^1551 := by
    have hnat : (2252530413 : ℕ)^2063*100000000000000^1551 ≤ 34624532624401^1551*5000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252530413 5000000000 34624532624401 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4251702953/10000000000 : ℝ)^2063 ≤ (32058851854837/100000000000000 : ℝ)^1551 := by
    have hnat : (4251702953 : ℕ)^2063*100000000000000^1551 ≤ 32058851854837^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251702953 10000000000 32058851854837 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218825527/500000000 : ℝ), (2252530413/5000000000 : ℝ), (4251702953/10000000000 : ℝ)] ![(3331661551233/10000000000000 : ℝ), (34624532624401/100000000000000 : ℝ), (32058851854837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218825527/500000000 : ℝ)|^2063 ≤ (3331661551233/10000000000000 : ℝ)^1551
        have hw : |(218825527/500000000 : ℝ)|=(218825527/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2252530413/5000000000 : ℝ)|^2063 ≤ (34624532624401/100000000000000 : ℝ)^1551
        have hw : |(2252530413/5000000000 : ℝ)|=(2252530413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4251702953/10000000000 : ℝ)|^2063 ≤ (32058851854837/100000000000000 : ℝ)^1551
        have hw : |(4251702953/10000000000 : ℝ)|=(4251702953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1059_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147856883/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13999/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5621/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5621/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6999/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13999/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5621/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13999/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5621/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13999/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5621/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13999/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5621/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13999/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5621/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13999/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5621/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5621/50000 : ℝ) ^ (8251/2048 : ℝ) ≤ (7498950148056113/50000000000000000000 : ℝ) := by
    have hpowers : (5621/50000 : ℝ)^8251 ≤ (7498950148056113/50000000000000000000 : ℝ)^2048 := by
      have hnat : (5621 : ℕ)^8251*50000000000000000000^2048 ≤ 7498950148056113^2048*50000^8251 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5621 50000 7498950148056113 50000000000000000000 8251 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5621/50000 : ℝ)) (X := (7498950148056113/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (13999/100000 : ℝ) ^ (8251/2048 : ℝ) ≤ (36290112114047311/100000000000000000000 : ℝ) := by
    have hpowers : (13999/100000 : ℝ)^8251 ≤ (36290112114047311/100000000000000000000 : ℝ)^2048 := by
      have hnat : (13999 : ℕ)^8251*100000000000000000000^2048 ≤ 36290112114047311^2048*100000^8251 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13999 100000 36290112114047311 100000000000000000000 8251 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13999/100000 : ℝ)) (X := (36290112114047311/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007498950148056113/25000000000000000000 : ℝ) ≤ (10000744448846083/10000000000000000 : ℝ) ^ (8251/2048 : ℝ) := by
    have hpowers : (25007498950148056113/25000000000000000000 : ℝ)^2048 ≤ (10000744448846083/10000000000000000 : ℝ)^8251 := by
      have hnat : (25007498950148056113 : ℕ)^2048*10000000000000000^8251 ≤ 10000744448846083^8251*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007498950148056113 25000000000000000000 10000744448846083 10000000000000000 2048 8251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000744448846083/10000000000000000 : ℝ)) (X := (25007498950148056113/25000000000000000000 : ℝ)) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051288012410159537/100000000000000000000 : ℝ) ≤ (2500318196598569/2500000000000000 : ℝ) ^ (8251/2048 : ℝ) := by
    have hpowers : (100051288012410159537/100000000000000000000 : ℝ)^2048 ≤ (2500318196598569/2500000000000000 : ℝ)^8251 := by
      have hnat : (100051288012410159537 : ℕ)^2048*2500000000000000^8251 ≤ 2500318196598569^8251*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051288012410159537 100000000000000000000 2500318196598569 2500000000000000 2048 8251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500318196598569/2500000000000000 : ℝ)) (X := (100051288012410159537/100000000000000000000 : ℝ)) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036290112114047311/50000000000000000000 : ℝ) ≤ (10001801123942469/10000000000000000 : ℝ) ^ (8251/2048 : ℝ) := by
    have hpowers : (50036290112114047311/50000000000000000000 : ℝ)^2048 ≤ (10001801123942469/10000000000000000 : ℝ)^8251 := by
      have hnat : (50036290112114047311 : ℕ)^2048*10000000000000000^8251 ≤ 10001801123942469^8251*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036290112114047311 50000000000000000000 10001801123942469 10000000000000000 2048 8251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001801123942469/10000000000000000 : ℝ)) (X := (50036290112114047311/50000000000000000000 : ℝ)) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7498950148056113/50000000000000000000 : ℝ) ≤ ((27560173304035079419/27570000000000000000 : ℝ)+2*(528337548193/275700000000000 : ℝ)*(5621/50000 : ℝ))^(8251/2048 : ℝ) := by
    rw [show (27560173304035079419/27570000000000000000 : ℝ)+2*(528337548193/275700000000000 : ℝ)*(5621/50000 : ℝ)=(10000744448846083/10000000000000000 : ℝ) by norm_num, show 1+2*(7498950148056113/50000000000000000000 : ℝ)=(25007498950148056113/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36290112114047311/100000000000000000000 : ℝ)+(7498950148056113/50000000000000000000 : ℝ) ≤ ((27560173304035079419/27570000000000000000 : ℝ)+(528337548193/275700000000000 : ℝ)*((13999/100000 : ℝ)+(5621/50000 : ℝ)))^(8251/2048 : ℝ) := by
    rw [show (27560173304035079419/27570000000000000000 : ℝ)+(528337548193/275700000000000 : ℝ)*((13999/100000 : ℝ)+(5621/50000 : ℝ))=(2500318196598569/2500000000000000 : ℝ) by norm_num, show 1+(36290112114047311/100000000000000000000 : ℝ)+(7498950148056113/50000000000000000000 : ℝ)=(100051288012410159537/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36290112114047311/100000000000000000000 : ℝ) ≤ ((27560173304035079419/27570000000000000000 : ℝ)+2*(528337548193/275700000000000 : ℝ)*(13999/100000 : ℝ))^(8251/2048 : ℝ) := by
    rw [show (27560173304035079419/27570000000000000000 : ℝ)+2*(528337548193/275700000000000 : ℝ)*(13999/100000 : ℝ)=(10001801123942469/10000000000000000 : ℝ) by norm_num, show 1+2*(36290112114047311/100000000000000000000 : ℝ)=(50036290112114047311/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27560173304035079419/27570000000000000000 : ℝ)*(X 1 0+X 2 0)+(528337548193/275700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8251/2048 : ℝ)) (lo := (5621/50000 : ℝ)) (hi := (13999/100000 : ℝ)) (c := (27560173304035079419/27570000000000000000 : ℝ)) (alpha := (528337548193/275700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27560173304035079419/27570000000000000000 : ℝ)*(X 0 1+X 2 1)+(528337548193/275700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8251/2048 : ℝ)) (lo := (5621/50000 : ℝ)) (hi := (13999/100000 : ℝ)) (c := (27560173304035079419/27570000000000000000 : ℝ)) (alpha := (528337548193/275700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27560173304035079419/27570000000000000000 : ℝ)*(X 0 2+X 1 2)+(528337548193/275700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8251/2048 : ℝ)) (lo := (5621/50000 : ℝ)) (hi := (13999/100000 : ℝ)) (c := (27560173304035079419/27570000000000000000 : ℝ)) (alpha := (528337548193/275700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5344989541/10000000000 : ℝ)*X 1 0+(-2273232593/10000000000 : ℝ)*X 1 1+(2632174183/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s9_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-1103611997/5000000000 : ℝ)*X 0 0+(5264674339/10000000000 : ℝ)*X 0 1+(2697063889/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s9_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1328059223/2500000000 : ℝ)*X 1 0+(-267931573/1250000000 : ℝ)*X 1 1+(5394127863/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s9_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2656118107/5000000000 : ℝ)*X 2 0+(67426599/125000000 : ℝ)*X 2 1+(-1071726711/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s9_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((218825527/500000000 : ℝ)*X 0 0+(2252530413/5000000000 : ℝ)*X 0 1+(4251702953/10000000000 : ℝ)*X 0 2+(218825527/500000000 : ℝ)*X 1 0+(2252530413/5000000000 : ℝ)*X 1 1+(4251702953/10000000000 : ℝ)*X 1 2+(218825527/500000000 : ℝ)*X 2 0+(2252530413/5000000000 : ℝ)*X 2 1+(4251702953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s9_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1640927653259046534691755767/229750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1134600441/100000000000000 : ℝ)*(base19) + (43881257/50000000000000 : ℝ)*(base23) + (28485511/50000000000000 : ℝ)*(lower1) + (189121457/100000000000000 : ℝ)*(lower3) + (149441/100000000000 : ℝ)*(lower4) + (30262193/50000000000000 : ℝ)*(lower5) + (5835870941405707/100000000000000 : ℝ)*(major0) + (5835870941405707/100000000000000 : ℝ)*(major1) + (5835870941405707/100000000000000 : ℝ)*(major2) + (6938629023/12500000000000 : ℝ)*(sp0) + (3862384426944601/50000000000000 : ℝ)*(sp1) + (7724712210256577/100000000000000 : ℝ)*(sp2) + (241399023941459/3125000000000 : ℝ)*(sp3) + (986743197711957/25000000000000 : ℝ)*(sp4) + (986743197711957/25000000000000 : ℝ)*(f.failure) + (3862384426944601/50000000000000 : ℝ)*(f.sum) + (13985611129169/13785000000000000000000000000 : ℝ)*base66 + (6287534516647944233/2757000000000000000000000000000000 : ℝ)*base67 + (3153057562309944233/2757000000000000000000000000000000 : ℝ)*base69 + (37879495043446055767/2757000000000000000000000000000000 : ℝ)*base72 + (47834964952771/13785000000000000000000000000 : ℝ)*base73 + (45572085488086944233/2757000000000000000000000000000000 : ℝ)*base75 + (3839282824525944233/2757000000000000000000000000000000 : ℝ)*base77 + (17648190050773944233/2757000000000000000000000000000000 : ℝ)*base79 + (31561194861271/13785000000000000000000000000 : ℝ)*base81 + (18850031/2500000000000000000000 : ℝ)*base89 + (18850031/2500000000000000000000 : ℝ)*base91 + (18850031/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1059_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147856883/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13999/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5621/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5621/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6999/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1059_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1059_box_0 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-519379247/2500000000 : ℝ)*x 0 + (1075492397/2000000000 : ℝ)*x 1 + (2688731243/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (519379247/2500000000 : ℝ)^2063 ≤ (6183430716379/50000000000000 : ℝ)^1551 := by
    have hnat : (519379247 : ℕ)^2063*50000000000000^1551 ≤ 6183430716379^1551*2500000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519379247 2500000000 6183430716379 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075492397/2000000000 : ℝ)^2063 ≤ (10954141640281/25000000000000 : ℝ)^1551 := by
    have hnat : (1075492397 : ℕ)^2063*25000000000000^1551 ≤ 10954141640281^1551*2000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075492397 2000000000 10954141640281 25000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688731243/5000000000 : ℝ)^2063 ≤ (43816571990953/100000000000000 : ℝ)^1551 := by
    have hnat : (2688731243 : ℕ)^2063*100000000000000^1551 ≤ 43816571990953^1551*5000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688731243 5000000000 43816571990953 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-519379247/2500000000 : ℝ), (1075492397/2000000000 : ℝ), (2688731243/5000000000 : ℝ)] ![(6183430716379/50000000000000 : ℝ), (10954141640281/25000000000000 : ℝ), (43816571990953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-519379247/2500000000 : ℝ)|^2063 ≤ (6183430716379/50000000000000 : ℝ)^1551
        have hw : |(-519379247/2500000000 : ℝ)|=(519379247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1075492397/2000000000 : ℝ)|^2063 ≤ (10954141640281/25000000000000 : ℝ)^1551
        have hw : |(1075492397/2000000000 : ℝ)|=(1075492397/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688731243/5000000000 : ℝ)|^2063 ≤ (43816571990953/100000000000000 : ℝ)^1551
        have hw : |(2688731243/5000000000 : ℝ)|=(2688731243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_box_1 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1323780727/2500000000 : ℝ)*x 0 + (-2188963737/10000000000 : ℝ)*x 1 + (672182767/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323780727/2500000000 : ℝ)^2063 ≤ (42926440224779/100000000000000 : ℝ)^1551 := by
    have hnat : (1323780727 : ℕ)^2063*100000000000000^1551 ≤ 42926440224779^1551*2500000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323780727 2500000000 42926440224779 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2188963737/10000000000 : ℝ)^2063 ≤ (13256991560517/100000000000000 : ℝ)^1551 := by
    have hnat : (2188963737 : ℕ)^2063*100000000000000^1551 ≤ 13256991560517^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188963737 10000000000 13256991560517 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (672182767/1250000000 : ℝ)^2063 ≤ (43816568197659/100000000000000 : ℝ)^1551 := by
    have hnat : (672182767 : ℕ)^2063*100000000000000^1551 ≤ 43816568197659^1551*1250000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672182767 1250000000 43816568197659 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323780727/2500000000 : ℝ), (-2188963737/10000000000 : ℝ), (672182767/1250000000 : ℝ)] ![(42926440224779/100000000000000 : ℝ), (13256991560517/100000000000000 : ℝ), (43816568197659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323780727/2500000000 : ℝ)|^2063 ≤ (42926440224779/100000000000000 : ℝ)^1551
        have hw : |(1323780727/2500000000 : ℝ)|=(1323780727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2188963737/10000000000 : ℝ)|^2063 ≤ (13256991560517/100000000000000 : ℝ)^1551
        have hw : |(-2188963737/10000000000 : ℝ)|=(2188963737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(672182767/1250000000 : ℝ)|^2063 ≤ (43816568197659/100000000000000 : ℝ)^1551
        have hw : |(672182767/1250000000 : ℝ)|=(672182767/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_box_2 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5295123023/10000000000 : ℝ)*x 0 + (5377462267/10000000000 : ℝ)*x 1 + (-1094481703/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295123023/10000000000 : ℝ)^2063 ≤ (21463220732407/50000000000000 : ℝ)^1551 := by
    have hnat : (5295123023 : ℕ)^2063*50000000000000^1551 ≤ 21463220732407^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295123023 10000000000 21463220732407 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377462267/10000000000 : ℝ)^2063 ≤ (8763313923487/20000000000000 : ℝ)^1551 := by
    have hnat : (5377462267 : ℕ)^2063*20000000000000^1551 ≤ 8763313923487^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377462267 10000000000 8763313923487 20000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1094481703/5000000000 : ℝ)^2063 ≤ (6628494447069/50000000000000 : ℝ)^1551 := by
    have hnat : (1094481703 : ℕ)^2063*50000000000000^1551 ≤ 6628494447069^1551*5000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094481703 5000000000 6628494447069 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295123023/10000000000 : ℝ), (5377462267/10000000000 : ℝ), (-1094481703/5000000000 : ℝ)] ![(21463220732407/50000000000000 : ℝ), (8763313923487/20000000000000 : ℝ), (6628494447069/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295123023/10000000000 : ℝ)|^2063 ≤ (21463220732407/50000000000000 : ℝ)^1551
        have hw : |(5295123023/10000000000 : ℝ)|=(5295123023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377462267/10000000000 : ℝ)|^2063 ≤ (8763313923487/20000000000000 : ℝ)^1551
        have hw : |(5377462267/10000000000 : ℝ)|=(5377462267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1094481703/5000000000 : ℝ)|^2063 ≤ (6628494447069/50000000000000 : ℝ)^1551
        have hw : |(-1094481703/5000000000 : ℝ)|=(1094481703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_box_3 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1121242329/2500000000 : ℝ)*x 0 + (4324434539/10000000000 : ℝ)*x 1 + (864886919/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1121242329/2500000000 : ℝ)^2063 ≤ (34419292085977/100000000000000 : ℝ)^1551 := by
    have hnat : (1121242329 : ℕ)^2063*100000000000000^1551 ≤ 34419292085977^1551*2500000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121242329 2500000000 34419292085977 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4324434539/10000000000 : ℝ)^2063 ≤ (16395176831781/50000000000000 : ℝ)^1551 := by
    have hnat : (4324434539 : ℕ)^2063*50000000000000^1551 ≤ 16395176831781^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324434539 10000000000 16395176831781 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (864886919/2000000000 : ℝ)^2063 ≤ (16395177114179/50000000000000 : ℝ)^1551 := by
    have hnat : (864886919 : ℕ)^2063*50000000000000^1551 ≤ 16395177114179^1551*2000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864886919 2000000000 16395177114179 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1121242329/2500000000 : ℝ), (4324434539/10000000000 : ℝ), (864886919/2000000000 : ℝ)] ![(34419292085977/100000000000000 : ℝ), (16395176831781/50000000000000 : ℝ), (16395177114179/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1121242329/2500000000 : ℝ)|^2063 ≤ (34419292085977/100000000000000 : ℝ)^1551
        have hw : |(1121242329/2500000000 : ℝ)|=(1121242329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4324434539/10000000000 : ℝ)|^2063 ≤ (16395176831781/50000000000000 : ℝ)^1551
        have hw : |(4324434539/10000000000 : ℝ)|=(4324434539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(864886919/2000000000 : ℝ)|^2063 ≤ (16395177114179/50000000000000 : ℝ)^1551
        have hw : |(864886919/2000000000 : ℝ)|=(864886919/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_box_4 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2338315269/10000000000 : ℝ)*x 0 + (2639992189/5000000000 : ℝ)*x 1 + (329998999/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2338315269/10000000000 : ℝ)^2063 ≤ (2894688930979/20000000000000 : ℝ)^1551 := by
    have hnat : (2338315269 : ℕ)^2063*20000000000000^1551 ≤ 2894688930979^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2338315269 10000000000 2894688930979 20000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2639992189/5000000000 : ℝ)^2063 ≤ (21381639895821/50000000000000 : ℝ)^1551 := by
    have hnat : (2639992189 : ℕ)^2063*50000000000000^1551 ≤ 21381639895821^1551*5000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639992189 5000000000 21381639895821 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329998999/625000000 : ℝ)^2063 ≤ (21381637773593/50000000000000 : ℝ)^1551 := by
    have hnat : (329998999 : ℕ)^2063*50000000000000^1551 ≤ 21381637773593^1551*625000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329998999 625000000 21381637773593 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2338315269/10000000000 : ℝ), (2639992189/5000000000 : ℝ), (329998999/625000000 : ℝ)] ![(2894688930979/20000000000000 : ℝ), (21381639895821/50000000000000 : ℝ), (21381637773593/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2338315269/10000000000 : ℝ)|^2063 ≤ (2894688930979/20000000000000 : ℝ)^1551
        have hw : |(-2338315269/10000000000 : ℝ)|=(2338315269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2639992189/5000000000 : ℝ)|^2063 ≤ (21381639895821/50000000000000 : ℝ)^1551
        have hw : |(2639992189/5000000000 : ℝ)|=(2639992189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329998999/625000000 : ℝ)|^2063 ≤ (21381637773593/50000000000000 : ℝ)^1551
        have hw : |(329998999/625000000 : ℝ)|=(329998999/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_box_5 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5364120949/10000000000 : ℝ)*x 0 + (-556762833/2500000000 : ℝ)*x 1 + (5279984323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364120949/10000000000 : ℝ)^2063 ≤ (21836017946929/50000000000000 : ℝ)^1551 := by
    have hnat : (5364120949 : ℕ)^2063*50000000000000^1551 ≤ 21836017946929^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364120949 10000000000 21836017946929 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (556762833/2500000000 : ℝ)^2063 ≤ (1356468488191/10000000000000 : ℝ)^1551 := by
    have hnat : (556762833 : ℕ)^2063*10000000000000^1551 ≤ 1356468488191^1551*2500000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      556762833 2500000000 1356468488191 10000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279984323/10000000000 : ℝ)^2063 ≤ (21381639599571/50000000000000 : ℝ)^1551 := by
    have hnat : (5279984323 : ℕ)^2063*50000000000000^1551 ≤ 21381639599571^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279984323 10000000000 21381639599571 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364120949/10000000000 : ℝ), (-556762833/2500000000 : ℝ), (5279984323/10000000000 : ℝ)] ![(21836017946929/50000000000000 : ℝ), (1356468488191/10000000000000 : ℝ), (21381639599571/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364120949/10000000000 : ℝ)|^2063 ≤ (21836017946929/50000000000000 : ℝ)^1551
        have hw : |(5364120949/10000000000 : ℝ)|=(5364120949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-556762833/2500000000 : ℝ)|^2063 ≤ (1356468488191/10000000000000 : ℝ)^1551
        have hw : |(-556762833/2500000000 : ℝ)|=(556762833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279984323/10000000000 : ℝ)|^2063 ≤ (21381639599571/50000000000000 : ℝ)^1551
        have hw : |(5279984323/10000000000 : ℝ)|=(5279984323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_box_6 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5364121519/10000000000 : ℝ)*x 0 + (2639991991/5000000000 : ℝ)*x 1 + (-139190689/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364121519/10000000000 : ℝ)^2063 ≤ (10918010516611/25000000000000 : ℝ)^1551 := by
    have hnat : (5364121519 : ℕ)^2063*25000000000000^1551 ≤ 10918010516611^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364121519 10000000000 10918010516611 25000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2639991991/5000000000 : ℝ)^2063 ≤ (42763275525641/100000000000000 : ℝ)^1551 := by
    have hnat : (2639991991 : ℕ)^2063*100000000000000^1551 ≤ 42763275525641^1551*5000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639991991 5000000000 42763275525641 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (139190689/625000000 : ℝ)^2063 ≤ (13564682386639/100000000000000 : ℝ)^1551 := by
    have hnat : (139190689 : ℕ)^2063*100000000000000^1551 ≤ 13564682386639^1551*625000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139190689 625000000 13564682386639 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364121519/10000000000 : ℝ), (2639991991/5000000000 : ℝ), (-139190689/625000000 : ℝ)] ![(10918010516611/25000000000000 : ℝ), (42763275525641/100000000000000 : ℝ), (13564682386639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364121519/10000000000 : ℝ)|^2063 ≤ (10918010516611/25000000000000 : ℝ)^1551
        have hw : |(5364121519/10000000000 : ℝ)|=(5364121519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2639991991/5000000000 : ℝ)|^2063 ≤ (42763275525641/100000000000000 : ℝ)^1551
        have hw : |(2639991991/5000000000 : ℝ)|=(2639991991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-139190689/625000000 : ℝ)|^2063 ≤ (13564682386639/100000000000000 : ℝ)^1551
        have hw : |(-139190689/625000000 : ℝ)|=(139190689/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_box_7 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (853541517/2000000000 : ℝ)*x 0 + (443304363/1000000000 : ℝ)*x 1 + (4433044203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (853541517/2000000000 : ℝ)^2063 ≤ (16109733722121/50000000000000 : ℝ)^1551 := by
    have hnat : (853541517 : ℕ)^2063*50000000000000^1551 ≤ 16109733722121^1551*2000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      853541517 2000000000 16109733722121 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (443304363/1000000000 : ℝ)^2063 ≤ (1694513167773/5000000000000 : ℝ)^1551 := by
    have hnat : (443304363 : ℕ)^2063*5000000000000^1551 ≤ 1694513167773^1551*1000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443304363 1000000000 1694513167773 5000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4433044203/10000000000 : ℝ)^2063 ≤ (33890269182057/100000000000000 : ℝ)^1551 := by
    have hnat : (4433044203 : ℕ)^2063*100000000000000^1551 ≤ 33890269182057^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4433044203 10000000000 33890269182057 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(853541517/2000000000 : ℝ), (443304363/1000000000 : ℝ), (4433044203/10000000000 : ℝ)] ![(16109733722121/50000000000000 : ℝ), (1694513167773/5000000000000 : ℝ), (33890269182057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(853541517/2000000000 : ℝ)|^2063 ≤ (16109733722121/50000000000000 : ℝ)^1551
        have hw : |(853541517/2000000000 : ℝ)|=(853541517/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(443304363/1000000000 : ℝ)|^2063 ≤ (1694513167773/5000000000000 : ℝ)^1551
        have hw : |(443304363/1000000000 : ℝ)|=(443304363/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4433044203/10000000000 : ℝ)|^2063 ≤ (33890269182057/100000000000000 : ℝ)^1551
        have hw : |(4433044203/10000000000 : ℝ)|=(4433044203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_box_8 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1141939937/5000000000 : ℝ)*x 0 + (5213853479/10000000000 : ℝ)*x 1 + (5387062057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1141939937/5000000000 : ℝ)^2063 ≤ (14027011036217/100000000000000 : ℝ)^1551 := by
    have hnat : (1141939937 : ℕ)^2063*100000000000000^1551 ≤ 14027011036217^1551*5000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141939937 5000000000 14027011036217 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5213853479/10000000000 : ℝ)^2063 ≤ (42052346327037/100000000000000 : ℝ)^1551 := by
    have hnat : (5213853479 : ℕ)^2063*100000000000000^1551 ≤ 42052346327037^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5213853479 10000000000 42052346327037 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387062057/10000000000 : ℝ)^2063 ≤ (2745040163413/6250000000000 : ℝ)^1551 := by
    have hnat : (5387062057 : ℕ)^2063*6250000000000^1551 ≤ 2745040163413^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387062057 10000000000 2745040163413 6250000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1141939937/5000000000 : ℝ), (5213853479/10000000000 : ℝ), (5387062057/10000000000 : ℝ)] ![(14027011036217/100000000000000 : ℝ), (42052346327037/100000000000000 : ℝ), (2745040163413/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1141939937/5000000000 : ℝ)|^2063 ≤ (14027011036217/100000000000000 : ℝ)^1551
        have hw : |(-1141939937/5000000000 : ℝ)|=(1141939937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5213853479/10000000000 : ℝ)|^2063 ≤ (42052346327037/100000000000000 : ℝ)^1551
        have hw : |(5213853479/10000000000 : ℝ)|=(5213853479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387062057/10000000000 : ℝ)|^2063 ≤ (2745040163413/6250000000000 : ℝ)^1551
        have hw : |(5387062057/10000000000 : ℝ)|=(5387062057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_box_9 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5288324017/10000000000 : ℝ)*x 0 + (-1092570983/5000000000 : ℝ)*x 1 + (5387062003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288324017/10000000000 : ℝ)^2063 ≤ (21426571944589/50000000000000 : ℝ)^1551 := by
    have hnat : (5288324017 : ℕ)^2063*50000000000000^1551 ≤ 21426571944589^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288324017 10000000000 21426571944589 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1092570983/5000000000 : ℝ)^2063 ≤ (206659594757/1562500000000 : ℝ)^1551 := by
    have hnat : (1092570983 : ℕ)^2063*1562500000000^1551 ≤ 206659594757^1551*5000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092570983 5000000000 206659594757 1562500000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387062003/10000000000 : ℝ)^2063 ≤ (10980160507253/25000000000000 : ℝ)^1551 := by
    have hnat : (5387062003 : ℕ)^2063*25000000000000^1551 ≤ 10980160507253^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387062003 10000000000 10980160507253 25000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288324017/10000000000 : ℝ), (-1092570983/5000000000 : ℝ), (5387062003/10000000000 : ℝ)] ![(21426571944589/50000000000000 : ℝ), (206659594757/1562500000000 : ℝ), (10980160507253/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288324017/10000000000 : ℝ)|^2063 ≤ (21426571944589/50000000000000 : ℝ)^1551
        have hw : |(5288324017/10000000000 : ℝ)|=(5288324017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1092570983/5000000000 : ℝ)|^2063 ≤ (206659594757/1562500000000 : ℝ)^1551
        have hw : |(-1092570983/5000000000 : ℝ)|=(1092570983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387062003/10000000000 : ℝ)|^2063 ≤ (10980160507253/25000000000000 : ℝ)^1551
        have hw : |(5387062003/10000000000 : ℝ)|=(5387062003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_box_10 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1322081021/2500000000 : ℝ)*x 0 + (2693531009/5000000000 : ℝ)*x 1 + (-68285683/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322081021/2500000000 : ℝ)^2063 ≤ (42853144611327/100000000000000 : ℝ)^1551 := by
    have hnat : (1322081021 : ℕ)^2063*100000000000000^1551 ≤ 42853144611327^1551*2500000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322081021 2500000000 42853144611327 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2693531009/5000000000 : ℝ)^2063 ≤ (21960321095839/50000000000000 : ℝ)^1551 := by
    have hnat : (2693531009 : ℕ)^2063*50000000000000^1551 ≤ 21960321095839^1551*5000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693531009 5000000000 21960321095839 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68285683/312500000 : ℝ)^2063 ≤ (13226213178851/100000000000000 : ℝ)^1551 := by
    have hnat : (68285683 : ℕ)^2063*100000000000000^1551 ≤ 13226213178851^1551*312500000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68285683 312500000 13226213178851 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322081021/2500000000 : ℝ), (2693531009/5000000000 : ℝ), (-68285683/312500000 : ℝ)] ![(42853144611327/100000000000000 : ℝ), (21960321095839/50000000000000 : ℝ), (13226213178851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322081021/2500000000 : ℝ)|^2063 ≤ (42853144611327/100000000000000 : ℝ)^1551
        have hw : |(1322081021/2500000000 : ℝ)|=(1322081021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2693531009/5000000000 : ℝ)|^2063 ≤ (21960321095839/50000000000000 : ℝ)^1551
        have hw : |(2693531009/5000000000 : ℝ)|=(2693531009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-68285683/312500000 : ℝ)|^2063 ≤ (13226213178851/100000000000000 : ℝ)^1551
        have hw : |(-68285683/312500000 : ℝ)|=(68285683/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_box_11 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4506092679/10000000000 : ℝ)*x 0 + (2156866149/5000000000 : ℝ)*x 1 + (4313732419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4506092679/10000000000 : ℝ)^2063 ≤ (34635081470087/100000000000000 : ℝ)^1551 := by
    have hnat : (4506092679 : ℕ)^2063*100000000000000^1551 ≤ 34635081470087^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506092679 10000000000 34635081470087 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2156866149/5000000000 : ℝ)^2063 ≤ (16341229322519/50000000000000 : ℝ)^1551 := by
    have hnat : (2156866149 : ℕ)^2063*50000000000000^1551 ≤ 16341229322519^1551*5000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156866149 5000000000 16341229322519 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4313732419/10000000000 : ℝ)^2063 ≤ (6536491972881/20000000000000 : ℝ)^1551 := by
    have hnat : (4313732419 : ℕ)^2063*20000000000000^1551 ≤ 6536491972881^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313732419 10000000000 6536491972881 20000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4506092679/10000000000 : ℝ), (2156866149/5000000000 : ℝ), (4313732419/10000000000 : ℝ)] ![(34635081470087/100000000000000 : ℝ), (16341229322519/50000000000000 : ℝ), (6536491972881/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4506092679/10000000000 : ℝ)|^2063 ≤ (34635081470087/100000000000000 : ℝ)^1551
        have hw : |(4506092679/10000000000 : ℝ)|=(4506092679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2156866149/5000000000 : ℝ)|^2063 ≤ (16341229322519/50000000000000 : ℝ)^1551
        have hw : |(2156866149/5000000000 : ℝ)|=(2156866149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4313732419/10000000000 : ℝ)|^2063 ≤ (6536491972881/20000000000000 : ℝ)^1551
        have hw : |(4313732419/10000000000 : ℝ)|=(4313732419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_box_12 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2132325553/10000000000 : ℝ)*x 0 + (2721125893/5000000000 : ℝ)*x 1 + (5271987109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2132325553/10000000000 : ℝ)^2063 ≤ (12802701149181/100000000000000 : ℝ)^1551 := by
    have hnat : (2132325553 : ℕ)^2063*100000000000000^1551 ≤ 12802701149181^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132325553 10000000000 12802701149181 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2721125893/5000000000 : ℝ)^2063 ≤ (44520149927729/100000000000000 : ℝ)^1551 := by
    have hnat : (2721125893 : ℕ)^2063*100000000000000^1551 ≤ 44520149927729^1551*5000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721125893 5000000000 44520149927729 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5271987109/10000000000 : ℝ)^2063 ≤ (10669287228111/25000000000000 : ℝ)^1551 := by
    have hnat : (5271987109 : ℕ)^2063*25000000000000^1551 ≤ 10669287228111^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271987109 10000000000 10669287228111 25000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2132325553/10000000000 : ℝ), (2721125893/5000000000 : ℝ), (5271987109/10000000000 : ℝ)] ![(12802701149181/100000000000000 : ℝ), (44520149927729/100000000000000 : ℝ), (10669287228111/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2132325553/10000000000 : ℝ)|^2063 ≤ (12802701149181/100000000000000 : ℝ)^1551
        have hw : |(-2132325553/10000000000 : ℝ)|=(2132325553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2721125893/5000000000 : ℝ)|^2063 ≤ (44520149927729/100000000000000 : ℝ)^1551
        have hw : |(2721125893/5000000000 : ℝ)|=(2721125893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5271987109/10000000000 : ℝ)|^2063 ≤ (10669287228111/25000000000000 : ℝ)^1551
        have hw : |(5271987109/10000000000 : ℝ)|=(5271987109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_box_13 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2684889797/5000000000 : ℝ)*x 0 + (-2230117161/10000000000 : ℝ)*x 1 + (5271986929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684889797/5000000000 : ℝ)^2063 ≤ (21866662292689/50000000000000 : ℝ)^1551 := by
    have hnat : (2684889797 : ℕ)^2063*50000000000000^1551 ≤ 21866662292689^1551*5000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684889797 5000000000 21866662292689 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2230117161/10000000000 : ℝ)^2063 ≤ (869729819/6400000000 : ℝ)^1551 := by
    have hnat : (2230117161 : ℕ)^2063*6400000000^1551 ≤ 869729819^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2230117161 10000000000 869729819 6400000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5271986929/10000000000 : ℝ)^2063 ≤ (42677146974323/100000000000000 : ℝ)^1551 := by
    have hnat : (5271986929 : ℕ)^2063*100000000000000^1551 ≤ 42677146974323^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271986929 10000000000 42677146974323 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684889797/5000000000 : ℝ), (-2230117161/10000000000 : ℝ), (5271986929/10000000000 : ℝ)] ![(21866662292689/50000000000000 : ℝ), (869729819/6400000000 : ℝ), (42677146974323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684889797/5000000000 : ℝ)|^2063 ≤ (21866662292689/50000000000000 : ℝ)^1551
        have hw : |(2684889797/5000000000 : ℝ)|=(2684889797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2230117161/10000000000 : ℝ)|^2063 ≤ (869729819/6400000000 : ℝ)^1551
        have hw : |(-2230117161/10000000000 : ℝ)|=(2230117161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5271986929/10000000000 : ℝ)|^2063 ≤ (42677146974323/100000000000000 : ℝ)^1551
        have hw : |(5271986929/10000000000 : ℝ)|=(5271986929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_box_14 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (536977907/1000000000 : ℝ)*x 0 + (527198717/1000000000 : ℝ)*x 1 + (-1115058771/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536977907/1000000000 : ℝ)^2063 ≤ (10933329727239/25000000000000 : ℝ)^1551 := by
    have hnat : (536977907 : ℕ)^2063*25000000000000^1551 ≤ 10933329727239^1551*1000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536977907 1000000000 10933329727239 25000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (527198717/1000000000 : ℝ)^2063 ≤ (10669287392313/25000000000000 : ℝ)^1551 := by
    have hnat : (527198717 : ℕ)^2063*25000000000000^1551 ≤ 10669287392313^1551*1000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527198717 1000000000 10669287392313 25000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1115058771/5000000000 : ℝ)^2063 ≤ (13589531509959/100000000000000 : ℝ)^1551 := by
    have hnat : (1115058771 : ℕ)^2063*100000000000000^1551 ≤ 13589531509959^1551*5000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115058771 5000000000 13589531509959 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536977907/1000000000 : ℝ), (527198717/1000000000 : ℝ), (-1115058771/5000000000 : ℝ)] ![(10933329727239/25000000000000 : ℝ), (10669287392313/25000000000000 : ℝ), (13589531509959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536977907/1000000000 : ℝ)|^2063 ≤ (10933329727239/25000000000000 : ℝ)^1551
        have hw : |(536977907/1000000000 : ℝ)|=(536977907/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(527198717/1000000000 : ℝ)|^2063 ≤ (10669287392313/25000000000000 : ℝ)^1551
        have hw : |(527198717/1000000000 : ℝ)|=(527198717/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1115058771/5000000000 : ℝ)|^2063 ≤ (13589531509959/100000000000000 : ℝ)^1551
        have hw : |(-1115058771/5000000000 : ℝ)|=(1115058771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_box_15 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (8300101/19531250 : ℝ)*x 0 + (4441949847/10000000000 : ℝ)*x 1 + (2220975177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8300101/19531250 : ℝ)^2063 ≤ (16019140446933/50000000000000 : ℝ)^1551 := by
    have hnat : (8300101 : ℕ)^2063*50000000000000^1551 ≤ 16019140446933^1551*19531250^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8300101 19531250 16019140446933 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4441949847/10000000000 : ℝ)^2063 ≤ (16990428482739/50000000000000 : ℝ)^1551 := by
    have hnat : (4441949847 : ℕ)^2063*50000000000000^1551 ≤ 16990428482739^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4441949847 10000000000 16990428482739 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2220975177/5000000000 : ℝ)^2063 ≤ (16990431062183/50000000000000 : ℝ)^1551 := by
    have hnat : (2220975177 : ℕ)^2063*50000000000000^1551 ≤ 16990431062183^1551*5000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2220975177 5000000000 16990431062183 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8300101/19531250 : ℝ), (4441949847/10000000000 : ℝ), (2220975177/5000000000 : ℝ)] ![(16019140446933/50000000000000 : ℝ), (16990428482739/50000000000000 : ℝ), (16990431062183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8300101/19531250 : ℝ)|^2063 ≤ (16019140446933/50000000000000 : ℝ)^1551
        have hw : |(8300101/19531250 : ℝ)|=(8300101/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4441949847/10000000000 : ℝ)|^2063 ≤ (16990428482739/50000000000000 : ℝ)^1551
        have hw : |(4441949847/10000000000 : ℝ)|=(4441949847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2220975177/5000000000 : ℝ)|^2063 ≤ (16990431062183/50000000000000 : ℝ)^1551
        have hw : |(2220975177/5000000000 : ℝ)|=(2220975177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1059_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147856883/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6999/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5621/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(3889/6250 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14809/25000 : ℝ) ∧ (1591/2000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (10367/12500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6999/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5621/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6999/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5621/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6999/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5621/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6999/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5621/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6999/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5621/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6999/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5621/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5621/50000 : ℝ) ^ (8251/2048 : ℝ) ≤ (7498950148056113/50000000000000000000 : ℝ) := by
    have hpowers : (5621/50000 : ℝ)^8251 ≤ (7498950148056113/50000000000000000000 : ℝ)^2048 := by
      have hnat : (5621 : ℕ)^8251*50000000000000000000^2048 ≤ 7498950148056113^2048*50000^8251 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5621 50000 7498950148056113 50000000000000000000 8251 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5621/50000 : ℝ)) (X := (7498950148056113/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (6999/50000 : ℝ) ^ (8251/2048 : ℝ) ≤ (36279669218137609/100000000000000000000 : ℝ) := by
    have hpowers : (6999/50000 : ℝ)^8251 ≤ (36279669218137609/100000000000000000000 : ℝ)^2048 := by
      have hnat : (6999 : ℕ)^8251*100000000000000000000^2048 ≤ 36279669218137609^2048*50000^8251 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6999 50000 36279669218137609 100000000000000000000 8251 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6999/50000 : ℝ)) (X := (36279669218137609/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007498950148056113/25000000000000000000 : ℝ) ≤ (10000744448846083/10000000000000000 : ℝ) ^ (8251/2048 : ℝ) := by
    have hpowers : (25007498950148056113/25000000000000000000 : ℝ)^2048 ≤ (10000744448846083/10000000000000000 : ℝ)^8251 := by
      have hnat : (25007498950148056113 : ℕ)^2048*10000000000000000^8251 ≤ 10000744448846083^8251*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007498950148056113 25000000000000000000 10000744448846083 10000000000000000 2048 8251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000744448846083/10000000000000000 : ℝ)) (X := (25007498950148056113/25000000000000000000 : ℝ)) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20010255513902849967/20000000000000000000 : ℝ) ≤ (2500318131822151/2500000000000000 : ℝ) ^ (8251/2048 : ℝ) := by
    have hpowers : (20010255513902849967/20000000000000000000 : ℝ)^2048 ≤ (2500318131822151/2500000000000000 : ℝ)^8251 := by
      have hnat : (20010255513902849967 : ℕ)^2048*2500000000000000^8251 ≤ 2500318131822151^8251*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20010255513902849967 20000000000000000000 2500318131822151 2500000000000000 2048 8251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500318131822151/2500000000000000 : ℝ)) (X := (20010255513902849967/20000000000000000000 : ℝ)) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036279669218137609/50000000000000000000 : ℝ) ≤ (80014404845849/80000000000000 : ℝ) ^ (8251/2048 : ℝ) := by
    have hpowers : (50036279669218137609/50000000000000000000 : ℝ)^2048 ≤ (80014404845849/80000000000000 : ℝ)^8251 := by
      have hnat : (50036279669218137609 : ℕ)^2048*80000000000000^8251 ≤ 80014404845849^8251*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036279669218137609 50000000000000000000 80014404845849 80000000000000 2048 8251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80014404845849/80000000000000 : ℝ)) (X := (50036279669218137609/50000000000000000000 : ℝ)) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7498950148056113/50000000000000000000 : ℝ) ≤ ((3443772298164770323/3445000000000000000 : ℝ)+2*(528078442521/275600000000000 : ℝ)*(5621/50000 : ℝ))^(8251/2048 : ℝ) := by
    rw [show (3443772298164770323/3445000000000000000 : ℝ)+2*(528078442521/275600000000000 : ℝ)*(5621/50000 : ℝ)=(10000744448846083/10000000000000000 : ℝ) by norm_num, show 1+2*(7498950148056113/50000000000000000000 : ℝ)=(25007498950148056113/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36279669218137609/100000000000000000000 : ℝ)+(7498950148056113/50000000000000000000 : ℝ) ≤ ((3443772298164770323/3445000000000000000 : ℝ)+(528078442521/275600000000000 : ℝ)*((6999/50000 : ℝ)+(5621/50000 : ℝ)))^(8251/2048 : ℝ) := by
    rw [show (3443772298164770323/3445000000000000000 : ℝ)+(528078442521/275600000000000 : ℝ)*((6999/50000 : ℝ)+(5621/50000 : ℝ))=(2500318131822151/2500000000000000 : ℝ) by norm_num, show 1+(36279669218137609/100000000000000000000 : ℝ)+(7498950148056113/50000000000000000000 : ℝ)=(20010255513902849967/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36279669218137609/100000000000000000000 : ℝ) ≤ ((3443772298164770323/3445000000000000000 : ℝ)+2*(528078442521/275600000000000 : ℝ)*(6999/50000 : ℝ))^(8251/2048 : ℝ) := by
    rw [show (3443772298164770323/3445000000000000000 : ℝ)+2*(528078442521/275600000000000 : ℝ)*(6999/50000 : ℝ)=(80014404845849/80000000000000 : ℝ) by norm_num, show 1+2*(36279669218137609/100000000000000000000 : ℝ)=(50036279669218137609/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3443772298164770323/3445000000000000000 : ℝ)*(X 1 0+X 2 0)+(528078442521/275600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8251/2048 : ℝ)) (lo := (5621/50000 : ℝ)) (hi := (6999/50000 : ℝ)) (c := (3443772298164770323/3445000000000000000 : ℝ)) (alpha := (528078442521/275600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3443772298164770323/3445000000000000000 : ℝ)*(X 0 1+X 2 1)+(528078442521/275600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8251/2048 : ℝ)) (lo := (5621/50000 : ℝ)) (hi := (6999/50000 : ℝ)) (c := (3443772298164770323/3445000000000000000 : ℝ)) (alpha := (528078442521/275600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3443772298164770323/3445000000000000000 : ℝ)*(X 0 2+X 1 2)+(528078442521/275600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8251/2048 : ℝ)) (lo := (5621/50000 : ℝ)) (hi := (6999/50000 : ℝ)) (c := (3443772298164770323/3445000000000000000 : ℝ)) (alpha := (528078442521/275600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-519379247/2500000000 : ℝ)*X 0 0+(1075492397/2000000000 : ℝ)*X 0 1+(2688731243/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1323780727/2500000000 : ℝ)*X 1 0+(-2188963737/10000000000 : ℝ)*X 1 1+(672182767/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5295123023/10000000000 : ℝ)*X 2 0+(5377462267/10000000000 : ℝ)*X 2 1+(-1094481703/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1121242329/2500000000 : ℝ)*X 0 0+(4324434539/10000000000 : ℝ)*X 0 1+(864886919/2000000000 : ℝ)*X 0 2+(1121242329/2500000000 : ℝ)*X 1 0+(4324434539/10000000000 : ℝ)*X 1 1+(864886919/2000000000 : ℝ)*X 1 2+(1121242329/2500000000 : ℝ)*X 2 0+(4324434539/10000000000 : ℝ)*X 2 1+(864886919/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2338315269/10000000000 : ℝ)*X 0 0+(2639992189/5000000000 : ℝ)*X 0 1+(329998999/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5364120949/10000000000 : ℝ)*X 1 0+(-556762833/2500000000 : ℝ)*X 1 1+(5279984323/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5364121519/10000000000 : ℝ)*X 2 0+(2639991991/5000000000 : ℝ)*X 2 1+(-139190689/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((853541517/2000000000 : ℝ)*X 0 0+(443304363/1000000000 : ℝ)*X 0 1+(4433044203/10000000000 : ℝ)*X 0 2+(853541517/2000000000 : ℝ)*X 1 0+(443304363/1000000000 : ℝ)*X 1 1+(4433044203/10000000000 : ℝ)*X 1 2+(853541517/2000000000 : ℝ)*X 2 0+(443304363/1000000000 : ℝ)*X 2 1+(4433044203/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1141939937/5000000000 : ℝ)*X 0 0+(5213853479/10000000000 : ℝ)*X 0 1+(5387062057/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5288324017/10000000000 : ℝ)*X 1 0+(-1092570983/5000000000 : ℝ)*X 1 1+(5387062003/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1322081021/2500000000 : ℝ)*X 2 0+(2693531009/5000000000 : ℝ)*X 2 1+(-68285683/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4506092679/10000000000 : ℝ)*X 0 0+(2156866149/5000000000 : ℝ)*X 0 1+(4313732419/10000000000 : ℝ)*X 0 2+(4506092679/10000000000 : ℝ)*X 1 0+(2156866149/5000000000 : ℝ)*X 1 1+(4313732419/10000000000 : ℝ)*X 1 2+(4506092679/10000000000 : ℝ)*X 2 0+(2156866149/5000000000 : ℝ)*X 2 1+(4313732419/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2132325553/10000000000 : ℝ)*X 0 0+(2721125893/5000000000 : ℝ)*X 0 1+(5271987109/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2684889797/5000000000 : ℝ)*X 1 0+(-2230117161/10000000000 : ℝ)*X 1 1+(5271986929/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((536977907/1000000000 : ℝ)*X 2 0+(527198717/1000000000 : ℝ)*X 2 1+(-1115058771/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((8300101/19531250 : ℝ)*X 0 0+(4441949847/10000000000 : ℝ)*X 0 1+(2220975177/5000000000 : ℝ)*X 0 2+(8300101/19531250 : ℝ)*X 1 0+(4441949847/10000000000 : ℝ)*X 1 1+(2220975177/5000000000 : ℝ)*X 1 2+(8300101/19531250 : ℝ)*X 2 0+(4441949847/10000000000 : ℝ)*X 2 1+(2220975177/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-3889/6250 : ℝ) ≤ (-1030546979414152710731452190199/1656250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (738253/2000000000000 : ℝ)*(upper0) + (132598413/50000000000000 : ℝ)*(lower1) + (300294041/100000000000000 : ℝ)*(lower2) + (481326300037491/12500000000000 : ℝ)*(major0) + (481326300037491/12500000000000 : ℝ)*(major1) + (481326300037491/12500000000000 : ℝ)*(major2) + (7436477719/50000000000000 : ℝ)*(sp1) + (6814217633/50000000000000 : ℝ)*(sp2) + (5117674251373397/100000000000000 : ℝ)*(sp4) + (511766435336891/10000000000000 : ℝ)*(sp5) + (2558832798944541/50000000000000 : ℝ)*(sp6) + (260422711120357/10000000000000 : ℝ)*(sp7) + (4974950951/100000000000000 : ℝ)*(sp8) + (13757802771/25000000000000 : ℝ)*(sp15) + (1302141071207327/50000000000000 : ℝ)*(f.failure) + (1279419806581087/25000000000000 : ℝ)*(f.sum) + (15999979167873/3445000000000000000000000000 : ℝ)*base66 + (487077116750129593/43062500000000000000000000000000 : ℝ)*base67 + (510640724777504593/43062500000000000000000000000000 : ℝ)*base69 + (268683076781317093/43062500000000000000000000000000 : ℝ)*base71 + (8274602191333/861250000000000000000000000 : ℝ)*base73 + (271038664775817093/43062500000000000000000000000000 : ℝ)*base75 + (186011026893942093/43062500000000000000000000000000 : ℝ)*base77 + (391939482110192093/43062500000000000000000000000000 : ℝ)*base79 + (704023072717/861250000000000000000000000 : ℝ)*base82 + (16981741/5000000000000000000000 : ℝ)*base89 + (16981741/5000000000000000000000 : ℝ)*base91 + (16981741/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (14809/25000 : ℝ) ≤ (48130908161712622121384783691/81250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16910701/100000000000000 : ℝ)*(lower0) + (34971189/20000000000000 : ℝ)*(lower3) + (13686929/12500000000000 : ℝ)*(upper4) + (195671107840883/5000000000000 : ℝ)*(major0) + (195671107840883/5000000000000 : ℝ)*(major1) + (195671107840883/5000000000000 : ℝ)*(major2) + (5160330971411201/100000000000000 : ℝ)*(sp0) + (5160331255826589/100000000000000 : ℝ)*(sp1) + (5160323987345529/100000000000000 : ℝ)*(sp2) + (33084494301463/1250000000000 : ℝ)*(sp3) + (861477223/25000000000000 : ℝ)*(sp5) + (167412343/1562500000000 : ℝ)*(sp6) + (4054177981/100000000000000 : ℝ)*(sp7) + (93258107/2500000000000 : ℝ)*(sp12) + (1323381799147511/50000000000000 : ℝ)*(f.failure) + (5160334701735481/100000000000000 : ℝ)*(f.sum) + (8384964057/1300000000000000000000000 : ℝ)*base65 + (4273290872503353/325000000000000000000000000000 : ℝ)*base67 + (2170706136953353/325000000000000000000000000000 : ℝ)*base69 + (4367217110753353/325000000000000000000000000000 : ℝ)*base71 + (2905596879/6500000000000000000000000 : ℝ)*base74 + (1660968982403353/325000000000000000000000000000 : ℝ)*base75 + (4389118231878353/325000000000000000000000000000 : ℝ)*base77 + (12230386266146647/325000000000000000000000000000 : ℝ)*base80 + (32977250329/6500000000000000000000000 : ℝ)*base81 + (33668213/5000000000000000000000 : ℝ)*base89 + (33668213/5000000000000000000000 : ℝ)*base91 + (33668213/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (1591/2000 : ℝ) ≤ (4282170144647040724649485574607/5382812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (17548689/50000000000000 : ℝ)*(upper0) + (55621363/100000000000000 : ℝ)*(lower3) + (5406569/10000000000000 : ℝ)*(upper4) + (547710610119519/12500000000000 : ℝ)*(major0) + (547710610119519/12500000000000 : ℝ)*(major1) + (547710610119519/12500000000000 : ℝ)*(major2) + (31828979701/100000000000000 : ℝ)*(sp1) + (54455794321/100000000000000 : ℝ)*(sp2) + (29807387403/100000000000000 : ℝ)*(sp3) + (285321387/50000000000000 : ℝ)*(sp4) + (2886694029228113/50000000000000 : ℝ)*(sp8) + (5773356800119299/100000000000000 : ℝ)*(sp9) + (5773334173304679/100000000000000 : ℝ)*(sp10) + (185214610903599/6250000000000 : ℝ)*(sp11) + (740865895461247/25000000000000 : ℝ)*(f.failure) + (5773388629099/100000000000 : ℝ)*(f.sum) + (798079778567/861250000000000000000000000 : ℝ)*base65 + (335540168889534637/43062500000000000000000000000000 : ℝ)*base67 + (519679040273534637/43062500000000000000000000000000 : ℝ)*base69 + (267850509352034637/43062500000000000000000000000000 : ℝ)*base71 + (19925741544897/861250000000000000000000000 : ℝ)*base73 + (486751354122597137/43062500000000000000000000000000 : ℝ)*base75 + (340783449071284637/43062500000000000000000000000000 : ℝ)*base77 + (1603782666608402863/43062500000000000000000000000000 : ℝ)*base80 + (9582494572497/3445000000000000000000000000 : ℝ)*base82 + (28713101/2500000000000000000000 : ℝ)*base89 + (28713101/2500000000000000000000 : ℝ)*base91 + (28713101/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-10367/12500 : ℝ) ≤ (-71426904288951270204137073914151/86125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16712521/50000000000000 : ℝ)*(lower0) + (759119/12500000000000 : ℝ)*(upper3) + (184135429/50000000000000 : ℝ)*(lower4) + (2208098459213493/50000000000000 : ℝ)*(major0) + (2208098459213493/50000000000000 : ℝ)*(major1) + (2208098459213493/50000000000000 : ℝ)*(major2) + (6434207637/50000000000000 : ℝ)*(sp0) + (30950238257/10000000000000 : ℝ)*(sp5) + (416522693719/100000000000000 : ℝ)*(sp6) + (142850223011/50000000000000 : ℝ)*(sp7) + (183538141761787/3125000000000 : ℝ)*(sp12) + (183528871950309/3125000000000 : ℝ)*(sp13) + (5872816882098739/100000000000000 : ℝ)*(sp14) + (373314924629919/12500000000000 : ℝ)*(sp15) + (1493402548742687/50000000000000 : ℝ)*(f.failure) + (2936616702396229/50000000000000 : ℝ)*(f.sum) + (13360372829153/6890000000000000000000000000 : ℝ)*base65 + (3569541938040230739/172250000000000000000000000000000 : ℝ)*base67 + (4168998675374230739/172250000000000000000000000000000 : ℝ)*base69 + (3408487606179730739/172250000000000000000000000000000 : ℝ)*base71 + (98722251821413/6890000000000000000000000000 : ℝ)*base73 + (2089825450589730739/172250000000000000000000000000000 : ℝ)*base75 + (2868665151199480739/172250000000000000000000000000000 : ℝ)*base77 + (10498956497568730739/172250000000000000000000000000000 : ℝ)*base79 + (22421044936653/6890000000000000000000000000 : ℝ)*base81 + (31135379/5000000000000000000000 : ℝ)*base90 + (31135379/5000000000000000000000 : ℝ)*base92 + (31135379/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1059_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147856883/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6999/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5621/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(14809/25000 : ℝ) else (1591/2000 : ℝ) ≤ X j i ∧ X j i ≤ (10367/12500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1059_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1059_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147856883/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13999/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5621/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(14809/25000 : ℝ) else (1591/2000 : ℝ) ≤ X j i ∧ X j i ≤ (10367/12500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1059_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1059_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147856883/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13999/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5621/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(14809/25000 : ℝ) else (1591/2000 : ℝ) ≤ X j i ∧ X j i ≤ (10367/12500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1059_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
