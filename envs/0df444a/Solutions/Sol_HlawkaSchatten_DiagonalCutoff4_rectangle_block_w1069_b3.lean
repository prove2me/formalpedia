-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1069_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:09:08.024747+00:00
-- url     : https://prove2.me/submissions/faa3913d-85d0-4a43-a04d-c6b4b75ef904

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
theorem support_rectangle_w1069_s9_0 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668120721/1250000000 : ℝ)*x 0 + (-226811883/1000000000 : ℝ)*x 1 + (5264534793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668120721/1250000000 : ℝ)^4131 ≤ (21739595791507/50000000000000 : ℝ)^3107 := by
    have hnat : (668120721 : ℕ)^4131*50000000000000^3107 ≤ 21739595791507^3107*1250000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668120721 1250000000 21739595791507 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226811883/1000000000 : ℝ)^4131 ≤ (2781872266389/20000000000000 : ℝ)^3107 := by
    have hnat : (226811883 : ℕ)^4131*20000000000000^3107 ≤ 2781872266389^3107*1000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226811883 1000000000 2781872266389 20000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264534793/10000000000 : ℝ)^4131 ≤ (10652861767261/25000000000000 : ℝ)^3107 := by
    have hnat : (5264534793 : ℕ)^4131*25000000000000^3107 ≤ 10652861767261^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264534793 10000000000 10652861767261 25000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668120721/1250000000 : ℝ), (-226811883/1000000000 : ℝ), (5264534793/10000000000 : ℝ)] ![(21739595791507/50000000000000 : ℝ), (2781872266389/20000000000000 : ℝ), (10652861767261/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668120721/1250000000 : ℝ)|^4131 ≤ (21739595791507/50000000000000 : ℝ)^3107
        have hw : |(668120721/1250000000 : ℝ)|=(668120721/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-226811883/1000000000 : ℝ)|^4131 ≤ (2781872266389/20000000000000 : ℝ)^3107
        have hw : |(-226811883/1000000000 : ℝ)|=(226811883/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264534793/10000000000 : ℝ)|^4131 ≤ (10652861767261/25000000000000 : ℝ)^3107
        have hw : |(5264534793/10000000000 : ℝ)|=(5264534793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s9_1 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2202297133/10000000000 : ℝ)*x 0 + (1052971911/2000000000 : ℝ)*x 1 + (5393951889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2202297133/10000000000 : ℝ)^4131 ≤ (13375253660901/100000000000000 : ℝ)^3107 := by
    have hnat : (2202297133 : ℕ)^4131*100000000000000^3107 ≤ 13375253660901^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202297133 10000000000 13375253660901 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052971911/2000000000 : ℝ)^4131 ≤ (21307471045251/50000000000000 : ℝ)^3107 := by
    have hnat : (1052971911 : ℕ)^4131*50000000000000^3107 ≤ 21307471045251^3107*2000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052971911 2000000000 21307471045251 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393951889/10000000000 : ℝ)^4131 ≤ (4400980423283/10000000000000 : ℝ)^3107 := by
    have hnat : (5393951889 : ℕ)^4131*10000000000000^3107 ≤ 4400980423283^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393951889 10000000000 4400980423283 10000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2202297133/10000000000 : ℝ), (1052971911/2000000000 : ℝ), (5393951889/10000000000 : ℝ)] ![(13375253660901/100000000000000 : ℝ), (21307471045251/50000000000000 : ℝ), (4400980423283/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2202297133/10000000000 : ℝ)|^4131 ≤ (13375253660901/100000000000000 : ℝ)^3107
        have hw : |(-2202297133/10000000000 : ℝ)|=(2202297133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052971911/2000000000 : ℝ)|^4131 ≤ (21307471045251/50000000000000 : ℝ)^3107
        have hw : |(1052971911/2000000000 : ℝ)|=(1052971911/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393951889/10000000000 : ℝ)|^4131 ≤ (4400980423283/10000000000000 : ℝ)^3107
        have hw : |(5393951889/10000000000 : ℝ)|=(5393951889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s9_2 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312278481/10000000000 : ℝ)*x 0 + (-427740219/2000000000 : ℝ)*x 1 + (5393952039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312278481/10000000000 : ℝ)^4131 ≤ (43126015846707/100000000000000 : ℝ)^3107 := by
    have hnat : (5312278481 : ℕ)^4131*100000000000000^3107 ≤ 43126015846707^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312278481 10000000000 43126015846707 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (427740219/2000000000 : ℝ)^4131 ≤ (2572835654627/20000000000000 : ℝ)^3107 := by
    have hnat : (427740219 : ℕ)^4131*20000000000000^3107 ≤ 2572835654627^3107*2000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427740219 2000000000 2572835654627 20000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393952039/10000000000 : ℝ)^4131 ≤ (8801961172011/20000000000000 : ℝ)^3107 := by
    have hnat : (5393952039 : ℕ)^4131*20000000000000^3107 ≤ 8801961172011^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393952039 10000000000 8801961172011 20000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312278481/10000000000 : ℝ), (-427740219/2000000000 : ℝ), (5393952039/10000000000 : ℝ)] ![(43126015846707/100000000000000 : ℝ), (2572835654627/20000000000000 : ℝ), (8801961172011/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312278481/10000000000 : ℝ)|^4131 ≤ (43126015846707/100000000000000 : ℝ)^3107
        have hw : |(5312278481/10000000000 : ℝ)|=(5312278481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-427740219/2000000000 : ℝ)|^4131 ≤ (2572835654627/20000000000000 : ℝ)^3107
        have hw : |(-427740219/2000000000 : ℝ)|=(427740219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393952039/10000000000 : ℝ)|^4131 ≤ (8801961172011/20000000000000 : ℝ)^3107
        have hw : |(5393952039/10000000000 : ℝ)|=(5393952039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s9_3 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656139259/5000000000 : ℝ)*x 0 + (8630323/16000000 : ℝ)*x 1 + (-2138701269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656139259/5000000000 : ℝ)^4131 ≤ (10781504061519/25000000000000 : ℝ)^3107 := by
    have hnat : (2656139259 : ℕ)^4131*25000000000000^3107 ≤ 10781504061519^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656139259 5000000000 10781504061519 25000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8630323/16000000 : ℝ)^4131 ≤ (11002451020239/25000000000000 : ℝ)^3107 := by
    have hnat : (8630323 : ℕ)^4131*25000000000000^3107 ≤ 11002451020239^3107*16000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8630323 16000000 11002451020239 25000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2138701269/10000000000 : ℝ)^4131 ≤ (6432089832337/50000000000000 : ℝ)^3107 := by
    have hnat : (2138701269 : ℕ)^4131*50000000000000^3107 ≤ 6432089832337^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138701269 10000000000 6432089832337 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656139259/5000000000 : ℝ), (8630323/16000000 : ℝ), (-2138701269/10000000000 : ℝ)] ![(10781504061519/25000000000000 : ℝ), (11002451020239/25000000000000 : ℝ), (6432089832337/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656139259/5000000000 : ℝ)|^4131 ≤ (10781504061519/25000000000000 : ℝ)^3107
        have hw : |(2656139259/5000000000 : ℝ)|=(2656139259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8630323/16000000 : ℝ)|^4131 ≤ (11002451020239/25000000000000 : ℝ)^3107
        have hw : |(8630323/16000000 : ℝ)|=(8630323/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2138701269/10000000000 : ℝ)|^4131 ≤ (6432089832337/50000000000000 : ℝ)^3107
        have hw : |(-2138701269/10000000000 : ℝ)|=(2138701269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_s9_4 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1093768079/2500000000 : ℝ)*x 0 + (4503512539/10000000000 : ℝ)*x 1 + (2125179569/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093768079/2500000000 : ℝ)^4131 ≤ (33316681312711/100000000000000 : ℝ)^3107 := by
    have hnat : (1093768079 : ℕ)^4131*100000000000000^3107 ≤ 33316681312711^3107*2500000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093768079 2500000000 33316681312711 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4503512539/10000000000 : ℝ)^4131 ≤ (34623375282587/100000000000000 : ℝ)^3107 := by
    have hnat : (4503512539 : ℕ)^4131*100000000000000^3107 ≤ 34623375282587^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503512539 10000000000 34623375282587 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2125179569/5000000000 : ℝ)^4131 ≤ (32059943395231/100000000000000 : ℝ)^3107 := by
    have hnat : (2125179569 : ℕ)^4131*100000000000000^3107 ≤ 32059943395231^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125179569 5000000000 32059943395231 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1093768079/2500000000 : ℝ), (4503512539/10000000000 : ℝ), (2125179569/5000000000 : ℝ)] ![(33316681312711/100000000000000 : ℝ), (34623375282587/100000000000000 : ℝ), (32059943395231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1093768079/2500000000 : ℝ)|^4131 ≤ (33316681312711/100000000000000 : ℝ)^3107
        have hw : |(1093768079/2500000000 : ℝ)|=(1093768079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4503512539/10000000000 : ℝ)|^4131 ≤ (34623375282587/100000000000000 : ℝ)^3107
        have hw : |(4503512539/10000000000 : ℝ)|=(4503512539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2125179569/5000000000 : ℝ)|^4131 ≤ (32059943395231/100000000000000 : ℝ)^3107
        have hw : |(2125179569/5000000000 : ℝ)|=(2125179569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1069_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74025701/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2801/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1407/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (1407/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3501/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2801/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1407/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2801/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1407/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2801/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1407/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2801/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1407/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2801/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1407/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2801/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1407/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1407/12500 : ℝ) ^ (8261/2048 : ℝ) ≤ (7456690849740531/50000000000000000000 : ℝ) := by
    have hpowers : (1407/12500 : ℝ)^8261 ≤ (7456690849740531/50000000000000000000 : ℝ)^2048 := by
      have hnat : (1407 : ℕ)^8261*50000000000000000000^2048 ≤ 7456690849740531^2048*12500^8261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1407 12500 7456690849740531 50000000000000000000 8261 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1407/12500 : ℝ)) (X := (7456690849740531/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2801/20000 : ℝ) ^ (8261/2048 : ℝ) ≤ (18002778351133023/50000000000000000000 : ℝ) := by
    have hpowers : (2801/20000 : ℝ)^8261 ≤ (18002778351133023/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2801 : ℕ)^8261*50000000000000000000^2048 ≤ 18002778351133023^2048*20000^8261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2801 20000 18002778351133023 50000000000000000000 8261 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2801/20000 : ℝ)) (X := (18002778351133023/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007456690849740531/25000000000000000000 : ℝ) ≤ (2500184839490403/2500000000000000 : ℝ) ^ (8261/2048 : ℝ) := by
    have hpowers : (25007456690849740531/25000000000000000000 : ℝ)^2048 ≤ (2500184839490403/2500000000000000 : ℝ)^8261 := by
      have hnat : (25007456690849740531 : ℕ)^2048*2500000000000000^8261 ≤ 2500184839490403^8261*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007456690849740531 25000000000000000000 2500184839490403 2500000000000000 2048 8261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500184839490403/2500000000000000 : ℝ)) (X := (25007456690849740531/25000000000000000000 : ℝ)) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012729734600436777/25000000000000000000 : ℝ) ≤ (2500315524827847/2500000000000000 : ℝ) ^ (8261/2048 : ℝ) := by
    have hpowers : (25012729734600436777/25000000000000000000 : ℝ)^2048 ≤ (2500315524827847/2500000000000000 : ℝ)^8261 := by
      have hnat : (25012729734600436777 : ℕ)^2048*2500000000000000^8261 ≤ 2500315524827847^8261*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012729734600436777 25000000000000000000 2500315524827847 2500000000000000 2048 8261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500315524827847/2500000000000000 : ℝ)) (X := (25012729734600436777/25000000000000000000 : ℝ)) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018002778351133023/25000000000000000000 : ℝ) ≤ (2500446210165291/2500000000000000 : ℝ) ^ (8261/2048 : ℝ) := by
    have hpowers : (25018002778351133023/25000000000000000000 : ℝ)^2048 ≤ (2500446210165291/2500000000000000 : ℝ)^8261 := by
      have hnat : (25018002778351133023 : ℕ)^2048*2500000000000000^8261 ≤ 2500446210165291^8261*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018002778351133023 25000000000000000000 2500446210165291 2500000000000000 2048 8261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500446210165291/2500000000000000 : ℝ)) (X := (25018002778351133023/25000000000000000000 : ℝ)) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7456690849740531/50000000000000000000 : ℝ) ≤ ((6870066135442578519/6872500000000000000 : ℝ)+2*(32671334361/17181250000000 : ℝ)*(1407/12500 : ℝ))^(8261/2048 : ℝ) := by
    rw [show (6870066135442578519/6872500000000000000 : ℝ)+2*(32671334361/17181250000000 : ℝ)*(1407/12500 : ℝ)=(2500184839490403/2500000000000000 : ℝ) by norm_num, show 1+2*(7456690849740531/50000000000000000000 : ℝ)=(25007456690849740531/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18002778351133023/50000000000000000000 : ℝ)+(7456690849740531/50000000000000000000 : ℝ) ≤ ((6870066135442578519/6872500000000000000 : ℝ)+(32671334361/17181250000000 : ℝ)*((2801/20000 : ℝ)+(1407/12500 : ℝ)))^(8261/2048 : ℝ) := by
    rw [show (6870066135442578519/6872500000000000000 : ℝ)+(32671334361/17181250000000 : ℝ)*((2801/20000 : ℝ)+(1407/12500 : ℝ))=(2500315524827847/2500000000000000 : ℝ) by norm_num, show 1+(18002778351133023/50000000000000000000 : ℝ)+(7456690849740531/50000000000000000000 : ℝ)=(25012729734600436777/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18002778351133023/50000000000000000000 : ℝ) ≤ ((6870066135442578519/6872500000000000000 : ℝ)+2*(32671334361/17181250000000 : ℝ)*(2801/20000 : ℝ))^(8261/2048 : ℝ) := by
    rw [show (6870066135442578519/6872500000000000000 : ℝ)+2*(32671334361/17181250000000 : ℝ)*(2801/20000 : ℝ)=(2500446210165291/2500000000000000 : ℝ) by norm_num, show 1+2*(18002778351133023/50000000000000000000 : ℝ)=(25018002778351133023/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6870066135442578519/6872500000000000000 : ℝ)*(X 1 0+X 2 0)+(32671334361/17181250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8261/2048 : ℝ)) (lo := (1407/12500 : ℝ)) (hi := (2801/20000 : ℝ)) (c := (6870066135442578519/6872500000000000000 : ℝ)) (alpha := (32671334361/17181250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6870066135442578519/6872500000000000000 : ℝ)*(X 0 1+X 2 1)+(32671334361/17181250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8261/2048 : ℝ)) (lo := (1407/12500 : ℝ)) (hi := (2801/20000 : ℝ)) (c := (6870066135442578519/6872500000000000000 : ℝ)) (alpha := (32671334361/17181250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6870066135442578519/6872500000000000000 : ℝ)*(X 0 2+X 1 2)+(32671334361/17181250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8261/2048 : ℝ)) (lo := (1407/12500 : ℝ)) (hi := (2801/20000 : ℝ)) (c := (6870066135442578519/6872500000000000000 : ℝ)) (alpha := (32671334361/17181250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((668120721/1250000000 : ℝ)*X 1 0+(-226811883/1000000000 : ℝ)*X 1 1+(5264534793/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s9_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-2202297133/10000000000 : ℝ)*X 0 0+(1052971911/2000000000 : ℝ)*X 0 1+(5393951889/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s9_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5312278481/10000000000 : ℝ)*X 1 0+(-427740219/2000000000 : ℝ)*X 1 1+(5393952039/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s9_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2656139259/5000000000 : ℝ)*X 2 0+(8630323/16000000 : ℝ)*X 2 1+(-2138701269/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s9_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((1093768079/2500000000 : ℝ)*X 0 0+(4503512539/10000000000 : ℝ)*X 0 1+(2125179569/5000000000 : ℝ)*X 0 2+(1093768079/2500000000 : ℝ)*X 1 0+(4503512539/10000000000 : ℝ)*X 1 1+(2125179569/5000000000 : ℝ)*X 1 2+(1093768079/2500000000 : ℝ)*X 2 0+(4503512539/10000000000 : ℝ)*X 2 1+(2125179569/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_s9_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (474544716297215674032484563/171812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (838355649/100000000000000 : ℝ)*(base19) + (854058381/100000000000000 : ℝ)*(base23) + (132118961/50000000000000 : ℝ)*(lower1) + (4550391/20000000000000 : ℝ)*(upper2) + (67576133/100000000000000 : ℝ)*(upper3) + (168328831/100000000000000 : ℝ)*(upper5) + (5848269031183159/100000000000000 : ℝ)*(major0) + (5848269031183159/100000000000000 : ℝ)*(major1) + (5848269031183159/100000000000000 : ℝ)*(major2) + (13176932273/100000000000000 : ℝ)*(sp0) + (1936594193702437/25000000000000 : ℝ)*(sp1) + (3873181379760913/50000000000000 : ℝ)*(sp2) + (968296990093921/12500000000000 : ℝ)*(sp3) + (3950161195490171/100000000000000 : ℝ)*(sp4) + (3950161195490171/100000000000000 : ℝ)*(f.failure) + (1936594193702437/25000000000000 : ℝ)*(f.sum) + (1503799532817/429531250000000000000000000 : ℝ)*base65 + (890057475472688479/687250000000000000000000000000000 : ℝ)*base68 + (582891267344938479/687250000000000000000000000000000 : ℝ)*base70 + (3526371362014061521/687250000000000000000000000000000 : ℝ)*base71 + (77950976394179/13745000000000000000000000000 : ℝ)*base73 + (6349306191474688479/687250000000000000000000000000000 : ℝ)*base76 + (4786917786197438479/687250000000000000000000000000000 : ℝ)*base78 + (6228253198507688479/687250000000000000000000000000000 : ℝ)*base80 + (10504146761457/6872500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (3115129/5000000000000000000000 : ℝ)*base90 + (3115129/5000000000000000000000 : ℝ)*base92 + (3115129/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1069_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74025701/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2801/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1407/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1407/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3501/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1069_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1069_box_0 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-414587979/2000000000 : ℝ)*x 0 + (5377325079/10000000000 : ℝ)*x 1 + (53773253/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (414587979/2000000000 : ℝ)^4131 ≤ (12340946532457/100000000000000 : ℝ)^3107 := by
    have hnat : (414587979 : ℕ)^4131*100000000000000^3107 ≤ 12340946532457^3107*2000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414587979 2000000000 12340946532457 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377325079/10000000000 : ℝ)^4131 ≤ (21914762763673/50000000000000 : ℝ)^3107 := by
    have hnat : (5377325079 : ℕ)^4131*50000000000000^3107 ≤ 21914762763673^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377325079 10000000000 21914762763673 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53773253/100000000 : ℝ)^4131 ≤ (2739345495147/6250000000000 : ℝ)^3107 := by
    have hnat : (53773253 : ℕ)^4131*6250000000000^3107 ≤ 2739345495147^3107*100000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53773253 100000000 2739345495147 6250000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-414587979/2000000000 : ℝ), (5377325079/10000000000 : ℝ), (53773253/100000000 : ℝ)] ![(12340946532457/100000000000000 : ℝ), (21914762763673/50000000000000 : ℝ), (2739345495147/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-414587979/2000000000 : ℝ)|^4131 ≤ (12340946532457/100000000000000 : ℝ)^3107
        have hw : |(-414587979/2000000000 : ℝ)|=(414587979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377325079/10000000000 : ℝ)|^4131 ≤ (21914762763673/50000000000000 : ℝ)^3107
        have hw : |(5377325079/10000000000 : ℝ)|=(5377325079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(53773253/100000000 : ℝ)|^4131 ≤ (2739345495147/6250000000000 : ℝ)^3107
        have hw : |(53773253/100000000 : ℝ)|=(53773253/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_box_1 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661904629/1250000000 : ℝ)*x 0 + (-546018417/2500000000 : ℝ)*x 1 + (5377325211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661904629/1250000000 : ℝ)^4131 ≤ (42942171975079/100000000000000 : ℝ)^3107 := by
    have hnat : (661904629 : ℕ)^4131*100000000000000^3107 ≤ 42942171975079^3107*1250000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661904629 1250000000 42942171975079 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (546018417/2500000000 : ℝ)^4131 ≤ (661415052469/5000000000000 : ℝ)^3107 := by
    have hnat : (546018417 : ℕ)^4131*5000000000000^3107 ≤ 661415052469^3107*2500000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546018417 2500000000 661415052469 5000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5377325211/10000000000 : ℝ)^4131 ≤ (43829526957847/100000000000000 : ℝ)^3107 := by
    have hnat : (5377325211 : ℕ)^4131*100000000000000^3107 ≤ 43829526957847^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377325211 10000000000 43829526957847 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661904629/1250000000 : ℝ), (-546018417/2500000000 : ℝ), (5377325211/10000000000 : ℝ)] ![(42942171975079/100000000000000 : ℝ), (661415052469/5000000000000 : ℝ), (43829526957847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661904629/1250000000 : ℝ)|^4131 ≤ (42942171975079/100000000000000 : ℝ)^3107
        have hw : |(661904629/1250000000 : ℝ)|=(661904629/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-546018417/2500000000 : ℝ)|^4131 ≤ (661415052469/5000000000000 : ℝ)^3107
        have hw : |(-546018417/2500000000 : ℝ)|=(546018417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5377325211/10000000000 : ℝ)|^4131 ≤ (43829526957847/100000000000000 : ℝ)^3107
        have hw : |(5377325211/10000000000 : ℝ)|=(5377325211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_box_2 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (264761839/500000000 : ℝ)*x 0 + (168041417/312500000 : ℝ)*x 1 + (-2184073827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264761839/500000000 : ℝ)^4131 ≤ (10735542314483/25000000000000 : ℝ)^3107 := by
    have hnat : (264761839 : ℕ)^4131*25000000000000^3107 ≤ 10735542314483^3107*500000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264761839 500000000 10735542314483 25000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168041417/312500000 : ℝ)^4131 ≤ (21914764199593/50000000000000 : ℝ)^3107 := by
    have hnat : (168041417 : ℕ)^4131*50000000000000^3107 ≤ 21914764199593^3107*312500000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168041417 312500000 21914764199593 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2184073827/10000000000 : ℝ)^4131 ≤ (6614151164893/50000000000000 : ℝ)^3107 := by
    have hnat : (2184073827 : ℕ)^4131*50000000000000^3107 ≤ 6614151164893^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184073827 10000000000 6614151164893 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264761839/500000000 : ℝ), (168041417/312500000 : ℝ), (-2184073827/10000000000 : ℝ)] ![(10735542314483/25000000000000 : ℝ), (21914764199593/50000000000000 : ℝ), (6614151164893/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264761839/500000000 : ℝ)|^4131 ≤ (10735542314483/25000000000000 : ℝ)^3107
        have hw : |(264761839/500000000 : ℝ)|=(264761839/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168041417/312500000 : ℝ)|^4131 ≤ (21914764199593/50000000000000 : ℝ)^3107
        have hw : |(168041417/312500000 : ℝ)|=(168041417/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2184073827/10000000000 : ℝ)|^4131 ≤ (6614151164893/50000000000000 : ℝ)^3107
        have hw : |(-2184073827/10000000000 : ℝ)|=(2184073827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_box_3 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2241706099/5000000000 : ℝ)*x 0 + (4323047393/10000000000 : ℝ)*x 1 + (2161523613/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2241706099/5000000000 : ℝ)^4131 ≤ (17209031357397/50000000000000 : ℝ)^3107 := by
    have hnat : (2241706099 : ℕ)^4131*50000000000000^3107 ≤ 17209031357397^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241706099 5000000000 17209031357397 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4323047393/10000000000 : ℝ)^4131 ≤ (32790969476063/100000000000000 : ℝ)^3107 := by
    have hnat : (4323047393 : ℕ)^4131*100000000000000^3107 ≤ 32790969476063^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4323047393 10000000000 32790969476063 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2161523613/5000000000 : ℝ)^4131 ≤ (32790967791859/100000000000000 : ℝ)^3107 := by
    have hnat : (2161523613 : ℕ)^4131*100000000000000^3107 ≤ 32790967791859^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161523613 5000000000 32790967791859 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2241706099/5000000000 : ℝ), (4323047393/10000000000 : ℝ), (2161523613/5000000000 : ℝ)] ![(17209031357397/50000000000000 : ℝ), (32790969476063/100000000000000 : ℝ), (32790967791859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2241706099/5000000000 : ℝ)|^4131 ≤ (17209031357397/50000000000000 : ℝ)^3107
        have hw : |(2241706099/5000000000 : ℝ)|=(2241706099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4323047393/10000000000 : ℝ)|^4131 ≤ (32790969476063/100000000000000 : ℝ)^3107
        have hw : |(4323047393/10000000000 : ℝ)|=(4323047393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2161523613/5000000000 : ℝ)|^4131 ≤ (32790967791859/100000000000000 : ℝ)^3107
        have hw : |(2161523613/5000000000 : ℝ)|=(2161523613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_box_4 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2333037097/10000000000 : ℝ)*x 0 + (5280135291/10000000000 : ℝ)*x 1 + (5280135269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2333037097/10000000000 : ℝ)^4131 ≤ (2888233394341/20000000000000 : ℝ)^3107 := by
    have hnat : (2333037097 : ℕ)^4131*20000000000000^3107 ≤ 2888233394341^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2333037097 10000000000 2888233394341 20000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5280135291/10000000000 : ℝ)^4131 ≤ (5347427077953/12500000000000 : ℝ)^3107 := by
    have hnat : (5280135291 : ℕ)^4131*12500000000000^3107 ≤ 5347427077953^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280135291 10000000000 5347427077953 12500000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280135269/10000000000 : ℝ)^4131 ≤ (10694854096659/25000000000000 : ℝ)^3107 := by
    have hnat : (5280135269 : ℕ)^4131*25000000000000^3107 ≤ 10694854096659^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280135269 10000000000 10694854096659 25000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2333037097/10000000000 : ℝ), (5280135291/10000000000 : ℝ), (5280135269/10000000000 : ℝ)] ![(2888233394341/20000000000000 : ℝ), (5347427077953/12500000000000 : ℝ), (10694854096659/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2333037097/10000000000 : ℝ)|^4131 ≤ (2888233394341/20000000000000 : ℝ)^3107
        have hw : |(-2333037097/10000000000 : ℝ)|=(2333037097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5280135291/10000000000 : ℝ)|^4131 ≤ (5347427077953/12500000000000 : ℝ)^3107
        have hw : |(5280135291/10000000000 : ℝ)|=(5280135291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280135269/10000000000 : ℝ)|^4131 ≤ (10694854096659/25000000000000 : ℝ)^3107
        have hw : |(5280135269/10000000000 : ℝ)|=(5280135269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_box_5 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5364015493/10000000000 : ℝ)*x 0 + (-555520061/2500000000 : ℝ)*x 1 + (5280135231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364015493/10000000000 : ℝ)^4131 ≤ (10921336658003/25000000000000 : ℝ)^3107 := by
    have hnat : (5364015493 : ℕ)^4131*25000000000000^3107 ≤ 10921336658003^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364015493 10000000000 10921336658003 25000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (555520061/2500000000 : ℝ)^4131 ≤ (3383809342987/25000000000000 : ℝ)^3107 := by
    have hnat : (555520061 : ℕ)^4131*25000000000000^3107 ≤ 3383809342987^3107*2500000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      555520061 2500000000 3383809342987 25000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280135231/10000000000 : ℝ)^4131 ≤ (42779415977293/100000000000000 : ℝ)^3107 := by
    have hnat : (5280135231 : ℕ)^4131*100000000000000^3107 ≤ 42779415977293^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280135231 10000000000 42779415977293 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364015493/10000000000 : ℝ), (-555520061/2500000000 : ℝ), (5280135231/10000000000 : ℝ)] ![(10921336658003/25000000000000 : ℝ), (3383809342987/25000000000000 : ℝ), (42779415977293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364015493/10000000000 : ℝ)|^4131 ≤ (10921336658003/25000000000000 : ℝ)^3107
        have hw : |(5364015493/10000000000 : ℝ)|=(5364015493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-555520061/2500000000 : ℝ)|^4131 ≤ (3383809342987/25000000000000 : ℝ)^3107
        have hw : |(-555520061/2500000000 : ℝ)|=(555520061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280135231/10000000000 : ℝ)|^4131 ≤ (42779415977293/100000000000000 : ℝ)^3107
        have hw : |(5280135231/10000000000 : ℝ)|=(5280135231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_box_6 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (670501921/1250000000 : ℝ)*x 0 + (5280135429/10000000000 : ℝ)*x 1 + (-2222080149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (670501921/1250000000 : ℝ)^4131 ≤ (10921336319619/25000000000000 : ℝ)^3107 := by
    have hnat : (670501921 : ℕ)^4131*25000000000000^3107 ≤ 10921336319619^3107*1250000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670501921 1250000000 10921336319619 25000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5280135429/10000000000 : ℝ)^4131 ≤ (8555883622037/20000000000000 : ℝ)^3107 := by
    have hnat : (5280135429 : ℕ)^4131*20000000000000^3107 ≤ 8555883622037^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280135429 10000000000 8555883622037 20000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2222080149/10000000000 : ℝ)^4131 ≤ (13535236602563/100000000000000 : ℝ)^3107 := by
    have hnat : (2222080149 : ℕ)^4131*100000000000000^3107 ≤ 13535236602563^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2222080149 10000000000 13535236602563 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(670501921/1250000000 : ℝ), (5280135429/10000000000 : ℝ), (-2222080149/10000000000 : ℝ)] ![(10921336319619/25000000000000 : ℝ), (8555883622037/20000000000000 : ℝ), (13535236602563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(670501921/1250000000 : ℝ)|^4131 ≤ (10921336319619/25000000000000 : ℝ)^3107
        have hw : |(670501921/1250000000 : ℝ)|=(670501921/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5280135429/10000000000 : ℝ)|^4131 ≤ (8555883622037/20000000000000 : ℝ)^3107
        have hw : |(5280135429/10000000000 : ℝ)|=(5280135429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2222080149/10000000000 : ℝ)|^4131 ≤ (13535236602563/100000000000000 : ℝ)^3107
        have hw : |(-2222080149/10000000000 : ℝ)|=(2222080149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_box_7 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (533297761/1250000000 : ℝ)*x 0 + (553942619/1250000000 : ℝ)*x 1 + (276971307/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (533297761/1250000000 : ℝ)^4131 ≤ (32220734872259/100000000000000 : ℝ)^3107 := by
    have hnat : (533297761 : ℕ)^4131*100000000000000^3107 ≤ 32220734872259^3107*1250000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533297761 1250000000 32220734872259 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (553942619/1250000000 : ℝ)^4131 ≤ (8472408190189/25000000000000 : ℝ)^3107 := by
    have hnat : (553942619 : ℕ)^4131*25000000000000^3107 ≤ 8472408190189^3107*1250000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553942619 1250000000 8472408190189 25000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (276971307/625000000 : ℝ)^4131 ≤ (6777926470809/20000000000000 : ℝ)^3107 := by
    have hnat : (276971307 : ℕ)^4131*20000000000000^3107 ≤ 6777926470809^3107*625000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276971307 625000000 6777926470809 20000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(533297761/1250000000 : ℝ), (553942619/1250000000 : ℝ), (276971307/625000000 : ℝ)] ![(32220734872259/100000000000000 : ℝ), (8472408190189/25000000000000 : ℝ), (6777926470809/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(533297761/1250000000 : ℝ)|^4131 ≤ (32220734872259/100000000000000 : ℝ)^3107
        have hw : |(533297761/1250000000 : ℝ)|=(533297761/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(553942619/1250000000 : ℝ)|^4131 ≤ (8472408190189/25000000000000 : ℝ)^3107
        have hw : |(553942619/1250000000 : ℝ)|=(553942619/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(276971307/625000000 : ℝ)|^4131 ≤ (6777926470809/20000000000000 : ℝ)^3107
        have hw : |(276971307/625000000 : ℝ)|=(276971307/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_box_8 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2278735533/10000000000 : ℝ)*x 0 + (1042836031/2000000000 : ℝ)*x 1 + (673365767/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2278735533/10000000000 : ℝ)^4131 ≤ (13995993565257/100000000000000 : ℝ)^3107 := by
    have hnat : (2278735533 : ℕ)^4131*100000000000000^3107 ≤ 13995993565257^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2278735533 10000000000 13995993565257 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042836031/2000000000 : ℝ)^4131 ≤ (2103520117579/5000000000000 : ℝ)^3107 := by
    have hnat : (1042836031 : ℕ)^4131*5000000000000^3107 ≤ 2103520117579^3107*2000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042836031 2000000000 2103520117579 5000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673365767/1250000000 : ℝ)^4131 ≤ (21966802032093/50000000000000 : ℝ)^3107 := by
    have hnat : (673365767 : ℕ)^4131*50000000000000^3107 ≤ 21966802032093^3107*1250000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673365767 1250000000 21966802032093 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2278735533/10000000000 : ℝ), (1042836031/2000000000 : ℝ), (673365767/1250000000 : ℝ)] ![(13995993565257/100000000000000 : ℝ), (2103520117579/5000000000000 : ℝ), (21966802032093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2278735533/10000000000 : ℝ)|^4131 ≤ (13995993565257/100000000000000 : ℝ)^3107
        have hw : |(-2278735533/10000000000 : ℝ)|=(2278735533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042836031/2000000000 : ℝ)|^4131 ≤ (2103520117579/5000000000000 : ℝ)^3107
        have hw : |(1042836031/2000000000 : ℝ)|=(1042836031/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673365767/1250000000 : ℝ)|^4131 ≤ (21966802032093/50000000000000 : ℝ)^3107
        have hw : |(673365767/1250000000 : ℝ)|=(673365767/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_box_9 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288439043/10000000000 : ℝ)*x 0 + (-1090124367/5000000000 : ℝ)*x 1 + (5386925983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288439043/10000000000 : ℝ)^4131 ≤ (1714755573531/4000000000000 : ℝ)^3107 := by
    have hnat : (5288439043 : ℕ)^4131*4000000000000^3107 ≤ 1714755573531^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288439043 10000000000 1714755573531 4000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1090124367/5000000000 : ℝ)^4131 ≤ (6598754121431/50000000000000 : ℝ)^3107 := by
    have hnat : (1090124367 : ℕ)^4131*50000000000000^3107 ≤ 6598754121431^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090124367 5000000000 6598754121431 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386925983/10000000000 : ℝ)^4131 ≤ (43933602405129/100000000000000 : ℝ)^3107 := by
    have hnat : (5386925983 : ℕ)^4131*100000000000000^3107 ≤ 43933602405129^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386925983 10000000000 43933602405129 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288439043/10000000000 : ℝ), (-1090124367/5000000000 : ℝ), (5386925983/10000000000 : ℝ)] ![(1714755573531/4000000000000 : ℝ), (6598754121431/50000000000000 : ℝ), (43933602405129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288439043/10000000000 : ℝ)|^4131 ≤ (1714755573531/4000000000000 : ℝ)^3107
        have hw : |(5288439043/10000000000 : ℝ)|=(5288439043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1090124367/5000000000 : ℝ)|^4131 ≤ (6598754121431/50000000000000 : ℝ)^3107
        have hw : |(-1090124367/5000000000 : ℝ)|=(1090124367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386925983/10000000000 : ℝ)|^4131 ≤ (43933602405129/100000000000000 : ℝ)^3107
        have hw : |(5386925983/10000000000 : ℝ)|=(5386925983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_box_10 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288439117/10000000000 : ℝ)*x 0 + (5386926093/10000000000 : ℝ)*x 1 + (-1090124243/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288439117/10000000000 : ℝ)^4131 ≤ (4286889013583/10000000000000 : ℝ)^3107 := by
    have hnat : (5288439117 : ℕ)^4131*10000000000000^3107 ≤ 4286889013583^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288439117 10000000000 4286889013583 10000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386926093/10000000000 : ℝ)^4131 ≤ (8786720719583/20000000000000 : ℝ)^3107 := by
    have hnat : (5386926093 : ℕ)^4131*20000000000000^3107 ≤ 8786720719583^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386926093 10000000000 8786720719583 20000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1090124243/5000000000 : ℝ)^4131 ≤ (1649688280863/12500000000000 : ℝ)^3107 := by
    have hnat : (1090124243 : ℕ)^4131*12500000000000^3107 ≤ 1649688280863^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090124243 5000000000 1649688280863 12500000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288439117/10000000000 : ℝ), (5386926093/10000000000 : ℝ), (-1090124243/5000000000 : ℝ)] ![(4286889013583/10000000000000 : ℝ), (8786720719583/20000000000000 : ℝ), (1649688280863/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288439117/10000000000 : ℝ)|^4131 ≤ (4286889013583/10000000000000 : ℝ)^3107
        have hw : |(5288439117/10000000000 : ℝ)|=(5288439117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386926093/10000000000 : ℝ)|^4131 ≤ (8786720719583/20000000000000 : ℝ)^3107
        have hw : |(5386926093/10000000000 : ℝ)|=(5386926093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1090124243/5000000000 : ℝ)|^4131 ≤ (1649688280863/12500000000000 : ℝ)^3107
        have hw : |(-1090124243/5000000000 : ℝ)|=(1090124243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_box_11 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1126144591/2500000000 : ℝ)*x 0 + (4312323537/10000000000 : ℝ)*x 1 + (1078080969/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1126144591/2500000000 : ℝ)^4131 ≤ (34634270472569/100000000000000 : ℝ)^3107 := by
    have hnat : (1126144591 : ℕ)^4131*100000000000000^3107 ≤ 34634270472569^3107*2500000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126144591 2500000000 34634270472569 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4312323537/10000000000 : ℝ)^4131 ≤ (16341431525027/50000000000000 : ℝ)^3107 := by
    have hnat : (4312323537 : ℕ)^4131*50000000000000^3107 ≤ 16341431525027^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4312323537 10000000000 16341431525027 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078080969/2500000000 : ℝ)^4131 ≤ (32682866466089/100000000000000 : ℝ)^3107 := by
    have hnat : (1078080969 : ℕ)^4131*100000000000000^3107 ≤ 32682866466089^3107*2500000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078080969 2500000000 32682866466089 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1126144591/2500000000 : ℝ), (4312323537/10000000000 : ℝ), (1078080969/2500000000 : ℝ)] ![(34634270472569/100000000000000 : ℝ), (16341431525027/50000000000000 : ℝ), (32682866466089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1126144591/2500000000 : ℝ)|^4131 ≤ (34634270472569/100000000000000 : ℝ)^3107
        have hw : |(1126144591/2500000000 : ℝ)|=(1126144591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4312323537/10000000000 : ℝ)|^4131 ≤ (16341431525027/50000000000000 : ℝ)^3107
        have hw : |(4312323537/10000000000 : ℝ)|=(4312323537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078080969/2500000000 : ℝ)|^4131 ≤ (32682866466089/100000000000000 : ℝ)^3107
        have hw : |(1078080969/2500000000 : ℝ)|=(1078080969/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_box_12 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2127608119/10000000000 : ℝ)*x 0 + (170060853/312500000 : ℝ)*x 1 + (1054426523/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2127608119/10000000000 : ℝ)^4131 ≤ (6387769908779/50000000000000 : ℝ)^3107 := by
    have hnat : (2127608119 : ℕ)^4131*50000000000000^3107 ≤ 6387769908779^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127608119 10000000000 6387769908779 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (170060853/312500000 : ℝ)^4131 ≤ (8906245658453/20000000000000 : ℝ)^3107 := by
    have hnat : (170060853 : ℕ)^4131*20000000000000^3107 ≤ 8906245658453^3107*312500000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170060853 312500000 8906245658453 20000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054426523/2000000000 : ℝ)^4131 ≤ (21346615932997/50000000000000 : ℝ)^3107 := by
    have hnat : (1054426523 : ℕ)^4131*50000000000000^3107 ≤ 21346615932997^3107*2000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054426523 2000000000 21346615932997 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2127608119/10000000000 : ℝ), (170060853/312500000 : ℝ), (1054426523/2000000000 : ℝ)] ![(6387769908779/50000000000000 : ℝ), (8906245658453/20000000000000 : ℝ), (21346615932997/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2127608119/10000000000 : ℝ)|^4131 ≤ (6387769908779/50000000000000 : ℝ)^3107
        have hw : |(-2127608119/10000000000 : ℝ)|=(2127608119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(170060853/312500000 : ℝ)|^4131 ≤ (8906245658453/20000000000000 : ℝ)^3107
        have hw : |(170060853/312500000 : ℝ)|=(170060853/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054426523/2000000000 : ℝ)|^4131 ≤ (21346615932997/50000000000000 : ℝ)^3107
        have hw : |(1054426523/2000000000 : ℝ)|=(1054426523/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_box_13 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369675929/10000000000 : ℝ)*x 0 + (-2225151013/10000000000 : ℝ)*x 1 + (2636066561/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369675929/10000000000 : ℝ)^4131 ≤ (10936662526501/25000000000000 : ℝ)^3107 := by
    have hnat : (5369675929 : ℕ)^4131*25000000000000^3107 ≤ 10936662526501^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369675929 10000000000 10936662526501 25000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2225151013/10000000000 : ℝ)^4131 ≤ (3390028135909/25000000000000 : ℝ)^3107 := by
    have hnat : (2225151013 : ℕ)^4131*25000000000000^3107 ≤ 3390028135909^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2225151013 10000000000 3390028135909 25000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636066561/5000000000 : ℝ)^4131 ≤ (42693237324761/100000000000000 : ℝ)^3107 := by
    have hnat : (2636066561 : ℕ)^4131*100000000000000^3107 ≤ 42693237324761^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636066561 5000000000 42693237324761 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369675929/10000000000 : ℝ), (-2225151013/10000000000 : ℝ), (2636066561/5000000000 : ℝ)] ![(10936662526501/25000000000000 : ℝ), (3390028135909/25000000000000 : ℝ), (42693237324761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369675929/10000000000 : ℝ)|^4131 ≤ (10936662526501/25000000000000 : ℝ)^3107
        have hw : |(5369675929/10000000000 : ℝ)|=(5369675929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2225151013/10000000000 : ℝ)|^4131 ≤ (3390028135909/25000000000000 : ℝ)^3107
        have hw : |(-2225151013/10000000000 : ℝ)|=(2225151013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636066561/5000000000 : ℝ)|^4131 ≤ (42693237324761/100000000000000 : ℝ)^3107
        have hw : |(2636066561/5000000000 : ℝ)|=(2636066561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_box_14 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (536967631/1000000000 : ℝ)*x 0 + (2636066229/5000000000 : ℝ)*x 1 + (-2225151387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536967631/1000000000 : ℝ)^4131 ≤ (8749330846603/20000000000000 : ℝ)^3107 := by
    have hnat : (536967631 : ℕ)^4131*20000000000000^3107 ≤ 8749330846603^3107*1000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536967631 1000000000 8749330846603 20000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2636066229/5000000000 : ℝ)^4131 ≤ (21346615087803/50000000000000 : ℝ)^3107 := by
    have hnat : (2636066229 : ℕ)^4131*50000000000000^3107 ≤ 21346615087803^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636066229 5000000000 21346615087803 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2225151387/10000000000 : ℝ)^4131 ≤ (6780057786981/50000000000000 : ℝ)^3107 := by
    have hnat : (2225151387 : ℕ)^4131*50000000000000^3107 ≤ 6780057786981^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2225151387 10000000000 6780057786981 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536967631/1000000000 : ℝ), (2636066229/5000000000 : ℝ), (-2225151387/10000000000 : ℝ)] ![(8749330846603/20000000000000 : ℝ), (21346615087803/50000000000000 : ℝ), (6780057786981/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536967631/1000000000 : ℝ)|^4131 ≤ (8749330846603/20000000000000 : ℝ)^3107
        have hw : |(536967631/1000000000 : ℝ)|=(536967631/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2636066229/5000000000 : ℝ)|^4131 ≤ (21346615087803/50000000000000 : ℝ)^3107
        have hw : |(2636066229/5000000000 : ℝ)|=(2636066229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2225151387/10000000000 : ℝ)|^4131 ≤ (6780057786981/50000000000000 : ℝ)^3107
        have hw : |(-2225151387/10000000000 : ℝ)|=(2225151387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1069_box_15 (p : ℝ) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (16594851/39062500 : ℝ)*x 0 + (2220234661/5000000000 : ℝ)*x 1 + (4440469177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16594851/39062500 : ℝ)^4131 ≤ (32039112327027/100000000000000 : ℝ)^3107 := by
    have hnat : (16594851 : ℕ)^4131*100000000000000^3107 ≤ 32039112327027^3107*39062500^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16594851 39062500 32039112327027 100000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2220234661/5000000000 : ℝ)^4131 ≤ (1699022228379/5000000000000 : ℝ)^3107 := by
    have hnat : (2220234661 : ℕ)^4131*5000000000000^3107 ≤ 1699022228379^3107*5000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2220234661 5000000000 1699022228379 5000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4440469177/10000000000 : ℝ)^4131 ≤ (16990221546137/50000000000000 : ℝ)^3107 := by
    have hnat : (4440469177 : ℕ)^4131*50000000000000^3107 ≤ 16990221546137^3107*10000000000^4131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4440469177 10000000000 16990221546137 50000000000000 4131 3107 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4131/1024 : ℝ)) 4131 3107 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16594851/39062500 : ℝ), (2220234661/5000000000 : ℝ), (4440469177/10000000000 : ℝ)] ![(32039112327027/100000000000000 : ℝ), (1699022228379/5000000000000 : ℝ), (16990221546137/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16594851/39062500 : ℝ)|^4131 ≤ (32039112327027/100000000000000 : ℝ)^3107
        have hw : |(16594851/39062500 : ℝ)|=(16594851/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2220234661/5000000000 : ℝ)|^4131 ≤ (1699022228379/5000000000000 : ℝ)^3107
        have hw : |(2220234661/5000000000 : ℝ)|=(2220234661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4440469177/10000000000 : ℝ)|^4131 ≤ (16990221546137/50000000000000 : ℝ)^3107
        have hw : |(4440469177/10000000000 : ℝ)|=(4440469177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1069_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74025701/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3501/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1407/12500 : ℝ)*pair X i i ≤ pair X i h) :
    -(2489/4000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59243/100000 : ℝ) ∧ (39791/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (82959/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3501/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1407/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3501/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1407/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3501/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1407/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3501/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1407/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3501/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1407/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3501/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1407/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1407/12500 : ℝ) ^ (8261/2048 : ℝ) ≤ (7456690849740531/50000000000000000000 : ℝ) := by
    have hpowers : (1407/12500 : ℝ)^8261 ≤ (7456690849740531/50000000000000000000 : ℝ)^2048 := by
      have hnat : (1407 : ℕ)^8261*50000000000000000000^2048 ≤ 7456690849740531^2048*12500^8261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1407 12500 7456690849740531 50000000000000000000 8261 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1407/12500 : ℝ)) (X := (7456690849740531/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3501/25000 : ℝ) ^ (8261/2048 : ℝ) ≤ (35995187578714139/100000000000000000000 : ℝ) := by
    have hpowers : (3501/25000 : ℝ)^8261 ≤ (35995187578714139/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3501 : ℕ)^8261*100000000000000000000^2048 ≤ 35995187578714139^2048*25000^8261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3501 25000 35995187578714139 100000000000000000000 8261 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3501/25000 : ℝ)) (X := (35995187578714139/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007456690849740531/25000000000000000000 : ℝ) ≤ (2500184839490403/2500000000000000 : ℝ) ^ (8261/2048 : ℝ) := by
    have hpowers : (25007456690849740531/25000000000000000000 : ℝ)^2048 ≤ (2500184839490403/2500000000000000 : ℝ)^8261 := by
      have hnat : (25007456690849740531 : ℕ)^2048*2500000000000000^8261 ≤ 2500184839490403^8261*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007456690849740531 25000000000000000000 2500184839490403 2500000000000000 2048 8261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500184839490403/2500000000000000 : ℝ)) (X := (25007456690849740531/25000000000000000000 : ℝ)) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050908569278195201/100000000000000000000 : ℝ) ≤ (10001261842346891/10000000000000000 : ℝ) ^ (8261/2048 : ℝ) := by
    have hpowers : (100050908569278195201/100000000000000000000 : ℝ)^2048 ≤ (10001261842346891/10000000000000000 : ℝ)^8261 := by
      have hnat : (100050908569278195201 : ℕ)^2048*10000000000000000^8261 ≤ 10001261842346891^8261*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050908569278195201 100000000000000000000 10001261842346891 10000000000000000 2048 8261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001261842346891/10000000000000000 : ℝ)) (X := (100050908569278195201/100000000000000000000 : ℝ)) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035995187578714139/50000000000000000000 : ℝ) ≤ (1000178432673217/1000000000000000 : ℝ) ^ (8261/2048 : ℝ) := by
    have hpowers : (50035995187578714139/50000000000000000000 : ℝ)^2048 ≤ (1000178432673217/1000000000000000 : ℝ)^8261 := by
      have hnat : (50035995187578714139 : ℕ)^2048*1000000000000000^8261 ≤ 1000178432673217^8261*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035995187578714139 50000000000000000000 1000178432673217 1000000000000000 2048 8261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000178432673217/1000000000000000 : ℝ)) (X := (50035995187578714139/50000000000000000000 : ℝ)) (by norm_num) 8261 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7456690849740531/50000000000000000000 : ℝ) ≤ ((143074320766651609/143125000000000000 : ℝ)+2*(522484385279/274800000000000 : ℝ)*(1407/12500 : ℝ))^(8261/2048 : ℝ) := by
    rw [show (143074320766651609/143125000000000000 : ℝ)+2*(522484385279/274800000000000 : ℝ)*(1407/12500 : ℝ)=(2500184839490403/2500000000000000 : ℝ) by norm_num, show 1+2*(7456690849740531/50000000000000000000 : ℝ)=(25007456690849740531/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35995187578714139/100000000000000000000 : ℝ)+(7456690849740531/50000000000000000000 : ℝ) ≤ ((143074320766651609/143125000000000000 : ℝ)+(522484385279/274800000000000 : ℝ)*((3501/25000 : ℝ)+(1407/12500 : ℝ)))^(8261/2048 : ℝ) := by
    rw [show (143074320766651609/143125000000000000 : ℝ)+(522484385279/274800000000000 : ℝ)*((3501/25000 : ℝ)+(1407/12500 : ℝ))=(10001261842346891/10000000000000000 : ℝ) by norm_num, show 1+(35995187578714139/100000000000000000000 : ℝ)+(7456690849740531/50000000000000000000 : ℝ)=(100050908569278195201/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35995187578714139/100000000000000000000 : ℝ) ≤ ((143074320766651609/143125000000000000 : ℝ)+2*(522484385279/274800000000000 : ℝ)*(3501/25000 : ℝ))^(8261/2048 : ℝ) := by
    rw [show (143074320766651609/143125000000000000 : ℝ)+2*(522484385279/274800000000000 : ℝ)*(3501/25000 : ℝ)=(1000178432673217/1000000000000000 : ℝ) by norm_num, show 1+2*(35995187578714139/100000000000000000000 : ℝ)=(50035995187578714139/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (143074320766651609/143125000000000000 : ℝ)*(X 1 0+X 2 0)+(522484385279/274800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8261/2048 : ℝ)) (lo := (1407/12500 : ℝ)) (hi := (3501/25000 : ℝ)) (c := (143074320766651609/143125000000000000 : ℝ)) (alpha := (522484385279/274800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (143074320766651609/143125000000000000 : ℝ)*(X 0 1+X 2 1)+(522484385279/274800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8261/2048 : ℝ)) (lo := (1407/12500 : ℝ)) (hi := (3501/25000 : ℝ)) (c := (143074320766651609/143125000000000000 : ℝ)) (alpha := (522484385279/274800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (143074320766651609/143125000000000000 : ℝ)*(X 0 2+X 1 2)+(522484385279/274800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8261/2048 : ℝ)) (lo := (1407/12500 : ℝ)) (hi := (3501/25000 : ℝ)) (c := (143074320766651609/143125000000000000 : ℝ)) (alpha := (522484385279/274800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-414587979/2000000000 : ℝ)*X 0 0+(5377325079/10000000000 : ℝ)*X 0 1+(53773253/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((661904629/1250000000 : ℝ)*X 1 0+(-546018417/2500000000 : ℝ)*X 1 1+(5377325211/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((264761839/500000000 : ℝ)*X 2 0+(168041417/312500000 : ℝ)*X 2 1+(-2184073827/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2241706099/5000000000 : ℝ)*X 0 0+(4323047393/10000000000 : ℝ)*X 0 1+(2161523613/5000000000 : ℝ)*X 0 2+(2241706099/5000000000 : ℝ)*X 1 0+(4323047393/10000000000 : ℝ)*X 1 1+(2161523613/5000000000 : ℝ)*X 1 2+(2241706099/5000000000 : ℝ)*X 2 0+(4323047393/10000000000 : ℝ)*X 2 1+(2161523613/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2333037097/10000000000 : ℝ)*X 0 0+(5280135291/10000000000 : ℝ)*X 0 1+(5280135269/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5364015493/10000000000 : ℝ)*X 1 0+(-555520061/2500000000 : ℝ)*X 1 1+(5280135231/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((670501921/1250000000 : ℝ)*X 2 0+(5280135429/10000000000 : ℝ)*X 2 1+(-2222080149/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((533297761/1250000000 : ℝ)*X 0 0+(553942619/1250000000 : ℝ)*X 0 1+(276971307/625000000 : ℝ)*X 0 2+(533297761/1250000000 : ℝ)*X 1 0+(553942619/1250000000 : ℝ)*X 1 1+(276971307/625000000 : ℝ)*X 1 2+(533297761/1250000000 : ℝ)*X 2 0+(553942619/1250000000 : ℝ)*X 2 1+(276971307/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2278735533/10000000000 : ℝ)*X 0 0+(1042836031/2000000000 : ℝ)*X 0 1+(673365767/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5288439043/10000000000 : ℝ)*X 1 0+(-1090124367/5000000000 : ℝ)*X 1 1+(5386925983/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5288439117/10000000000 : ℝ)*X 2 0+(5386926093/10000000000 : ℝ)*X 2 1+(-1090124243/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1126144591/2500000000 : ℝ)*X 0 0+(4312323537/10000000000 : ℝ)*X 0 1+(1078080969/2500000000 : ℝ)*X 0 2+(1126144591/2500000000 : ℝ)*X 1 0+(4312323537/10000000000 : ℝ)*X 1 1+(1078080969/2500000000 : ℝ)*X 1 2+(1126144591/2500000000 : ℝ)*X 2 0+(4312323537/10000000000 : ℝ)*X 2 1+(1078080969/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2127608119/10000000000 : ℝ)*X 0 0+(170060853/312500000 : ℝ)*X 0 1+(1054426523/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5369675929/10000000000 : ℝ)*X 1 0+(-2225151013/10000000000 : ℝ)*X 1 1+(2636066561/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((536967631/1000000000 : ℝ)*X 2 0+(2636066229/5000000000 : ℝ)*X 2 1+(-2225151387/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((16594851/39062500 : ℝ)*X 0 0+(2220234661/5000000000 : ℝ)*X 0 1+(4440469177/10000000000 : ℝ)*X 0 2+(16594851/39062500 : ℝ)*X 1 0+(2220234661/5000000000 : ℝ)*X 1 1+(4440469177/10000000000 : ℝ)*X 1 2+(16594851/39062500 : ℝ)*X 2 0+(2220234661/5000000000 : ℝ)*X 2 1+(4440469177/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1069_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-2489/4000 : ℝ) ≤ (-1424888046229415295428567847/2290000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10888493/100000000000000 : ℝ)*(upper0) + (9070011/25000000000000 : ℝ)*(upper1) + (22497/78125000000 : ℝ)*(upper5) + (1929605776586189/50000000000000 : ℝ)*(major0) + (1929605776586189/50000000000000 : ℝ)*(major1) + (1929605776586189/50000000000000 : ℝ)*(major2) + (6973613/400000000000 : ℝ)*(sp1) + (965456673/100000000000000 : ℝ)*(sp3) + (513249062810387/10000000000000 : ℝ)*(sp4) + (5132492042339589/100000000000000 : ℝ)*(sp5) + (1026480327243197/20000000000000 : ℝ)*(sp6) + (1303334541810093/50000000000000 : ℝ)*(sp7) + (3157638969/100000000000000 : ℝ)*(sp8) + (18429905371/20000000000000 : ℝ)*(sp14) + (130333502453843/5000000000000 : ℝ)*(f.failure) + (128312344643571/2500000000000 : ℝ)*(f.sum) + (16147491255119/6870000000000000000000000000 : ℝ)*base66 + (415156284091797019/42937500000000000000000000000000 : ℝ)*base68 + (422752857372827981/42937500000000000000000000000000 : ℝ)*base69 + (4908359961265481/42937500000000000000000000000000 : ℝ)*base71 + (188337755823419/6870000000000000000000000000 : ℝ)*base74 + (424096329025015481/42937500000000000000000000000000 : ℝ)*base75 + (56799532358172019/42937500000000000000000000000000 : ℝ)*base78 + (169023754574922019/42937500000000000000000000000000 : ℝ)*base80 + (24615689067869/6870000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (3218943/250000000000000000000 : ℝ)*base89 + (3218943/250000000000000000000 : ℝ)*base91 + (3218943/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (59243/100000 : ℝ) ≤ (2119879503776728348771116798201/3578125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (51363723/50000000000000 : ℝ)*(upper1) + (156104087/100000000000000 : ℝ)*(upper2) + (4799729/25000000000000 : ℝ)*(upper3) + (8676663/50000000000000 : ℝ)*(upper4) + (490270878753311/12500000000000 : ℝ)*(major0) + (490270878753311/12500000000000 : ℝ)*(major1) + (490270878753311/12500000000000 : ℝ)*(major2) + (5175386218445409/100000000000000 : ℝ)*(sp0) + (5175381822944787/100000000000000 : ℝ)*(sp1) + (646922879277903/12500000000000 : ℝ)*(sp2) + (331149095604857/12500000000000 : ℝ)*(sp3) + (5479348511/50000000000000 : ℝ)*(sp5) + (1949483717/20000000000000 : ℝ)*(sp6) + (16407991/250000000000 : ℝ)*(sp12) + (331149095604857/12500000000000 : ℝ)*(f.failure) + (5175392781641809/100000000000000 : ℝ)*(f.sum) + (19722426978817/3435000000000000000000000000 : ℝ)*base66 + (20072632677999053/5367187500000000000000000000000 : ℝ)*base68 + (526492355715580019/10734375000000000000000000000000 : ℝ)*base69 + (85565952607763731/10734375000000000000000000000000 : ℝ)*base72 + (3602640897701/1717500000000000000000000000 : ℝ)*base74 + (2633413959342803/5367187500000000000000000000000 : ℝ)*base76 + (87810284676357481/10734375000000000000000000000000 : ℝ)*base78 + (13833843850601089/2683593750000000000000000000000 : ℝ)*base80 + (323600259833/3435000000000000000000000000 : ℝ)*base81 + (8429757/625000000000000000000 : ℝ)*base89 + (8429757/625000000000000000000 : ℝ)*base91 + (8429757/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (39791/50000 : ℝ) ≤ (455619595316253021536908519/572500000000000000000000000 : ℝ) := by norm_num
    linear_combination (99451633/100000000000000 : ℝ)*(upper0) + (54437349/50000000000000 : ℝ)*(lower3) + (1329819/1250000000000 : ℝ)*(upper4) + (1097606833174717/25000000000000 : ℝ)*(major0) + (1097606833174717/25000000000000 : ℝ)*(major1) + (1097606833174717/25000000000000 : ℝ)*(major2) + (1647963981/3125000000000 : ℝ)*(sp1) + (146222473073/100000000000000 : ℝ)*(sp2) + (48296342261/100000000000000 : ℝ)*(sp3) + (1419796263/50000000000000 : ℝ)*(sp4) + (5788848743213849/100000000000000 : ℝ)*(sp8) + (5788798847958983/100000000000000 : ℝ)*(sp9) + (2894352680166651/50000000000000 : ℝ)*(sp10) + (2965426716652799/100000000000000 : ℝ)*(sp11) + (148273750649753/5000000000000 : ℝ)*(f.failure) + (46310812662451/800000000000 : ℝ)*(f.sum) + (5540731415959/1717500000000000000000000000 : ℝ)*base65 + (204268619113441457/21468750000000000000000000000000 : ℝ)*base68 + (207415864247097707/21468750000000000000000000000000 : ℝ)*base70 + (86746147461246043/21468750000000000000000000000000 : ℝ)*base71 + (150470871585187/3435000000000000000000000000 : ℝ)*base74 + (21365912142246043/21468750000000000000000000000000 : ℝ)*base75 + (94968561470402293/21468750000000000000000000000000 : ℝ)*base77 + (817238133235910207/21468750000000000000000000000000 : ℝ)*base80 + (12373306759301/1717500000000000000000000000 : ℝ)*base82 + (1301853/250000000000000000000 : ℝ)*base89 + (1301853/250000000000000000000 : ℝ)*base91 + (1301853/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-82959/100000 : ℝ) ≤ (-2968298088819921030186594912091/3578125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (906091/20000000000000 : ℝ)*(upper2) + (1869269/1000000000000 : ℝ)*(upper3) + (32127439/100000000000000 : ℝ)*(lower4) + (64961293/100000000000000 : ℝ)*(upper5) + (2212486186163567/50000000000000 : ℝ)*(major0) + (2212486186163567/50000000000000 : ℝ)*(major1) + (2212486186163567/50000000000000 : ℝ)*(major2) + (10612401081/100000000000000 : ℝ)*(sp0) + (57636334529/12500000000000 : ℝ)*(sp6) + (21301325719/25000000000000 : ℝ)*(sp7) + (5888778247611609/100000000000000 : ℝ)*(sp12) + (5888788860012691/100000000000000 : ℝ)*(sp13) + (5888327769336459/100000000000000 : ℝ)*(sp14) + (1494361473416391/50000000000000 : ℝ)*(sp15) + (1494404076067829/50000000000000 : ℝ)*(f.failure) + (5888788860012691/100000000000000 : ℝ)*(f.sum) + (492303693560987/6870000000000000000000000000 : ℝ)*base66 + (145015001294916443/42937500000000000000000000000000 : ℝ)*base67 + (112899343439708557/42937500000000000000000000000000 : ℝ)*base70 + (3600897239580083557/42937500000000000000000000000000 : ℝ)*base72 + (26271542669683/6870000000000000000000000000 : ℝ)*base73 + (175156559133478943/42937500000000000000000000000000 : ℝ)*base75 + (199161123795646057/42937500000000000000000000000000 : ℝ)*base78 + (346376351190646057/42937500000000000000000000000000 : ℝ)*base80 + (22792625748557/6870000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (15273129/2500000000000000000000 : ℝ)*base89 + (15273129/2500000000000000000000 : ℝ)*base91 + (15273129/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1069_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74025701/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3501/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1407/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(59243/100000 : ℝ) else (39791/50000 : ℝ) ≤ X j i ∧ X j i ≤ (82959/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1069_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1069_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74025701/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2801/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1407/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(59243/100000 : ℝ) else (39791/50000 : ℝ) ≤ X j i ∧ X j i ≤ (82959/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1069_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1069_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8261/2048 : ℝ) ≤ p) (hpb : p ≤ (4131/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74025701/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2801/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1407/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(59243/100000 : ℝ) else (39791/50000 : ℝ) ≤ X j i ∧ X j i ≤ (82959/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1069_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
