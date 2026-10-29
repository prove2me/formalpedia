-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1568_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:27:07.216795+00:00
-- url     : https://prove2.me/submissions/07f3d6fc-484b-41b0-beb5-5a376eb319e9

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
theorem support_rectangle_w1568_s3_0 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-894047663/5000000000 : ℝ)*x 0 + (5427756351/10000000000 : ℝ)*x 1 + (5218450723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (894047663/5000000000 : ℝ)^4633 ≤ (10971541606163/100000000000000 : ℝ)^3609 := by
    have hnat : (894047663 : ℕ)^4633*100000000000000^3609 ≤ 10971541606163^3609*5000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894047663 5000000000 10971541606163 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427756351/10000000000 : ℝ)^4633 ≤ (9127520455171/20000000000000 : ℝ)^3609 := by
    have hnat : (5427756351 : ℕ)^4633*20000000000000^3609 ≤ 9127520455171^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427756351 10000000000 9127520455171 20000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218450723/10000000000 : ℝ)^4633 ≤ (43390856103351/100000000000000 : ℝ)^3609 := by
    have hnat : (5218450723 : ℕ)^4633*100000000000000^3609 ≤ 43390856103351^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218450723 10000000000 43390856103351 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-894047663/5000000000 : ℝ), (5427756351/10000000000 : ℝ), (5218450723/10000000000 : ℝ)] ![(10971541606163/100000000000000 : ℝ), (9127520455171/20000000000000 : ℝ), (43390856103351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-894047663/5000000000 : ℝ)|^4633 ≤ (10971541606163/100000000000000 : ℝ)^3609
        have hw : |(-894047663/5000000000 : ℝ)|=(894047663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427756351/10000000000 : ℝ)|^4633 ≤ (9127520455171/20000000000000 : ℝ)^3609
        have hw : |(5427756351/10000000000 : ℝ)|=(5427756351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218450723/10000000000 : ℝ)|^4633 ≤ (43390856103351/100000000000000 : ℝ)^3609
        have hw : |(5218450723/10000000000 : ℝ)|=(5218450723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s3_1 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337191717/2500000000 : ℝ)*x 0 + (-118450933/625000000 : ℝ)*x 1 + (2609225429/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337191717/2500000000 : ℝ)^4633 ≤ (4478676509529/10000000000000 : ℝ)^3609 := by
    have hnat : (1337191717 : ℕ)^4633*10000000000000^3609 ≤ 4478676509529^3609*2500000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337191717 2500000000 4478676509529 10000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (118450933/625000000 : ℝ)^4633 ≤ (2955594336597/25000000000000 : ℝ)^3609 := by
    have hnat : (118450933 : ℕ)^4633*25000000000000^3609 ≤ 2955594336597^3609*625000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118450933 625000000 2955594336597 25000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609225429/5000000000 : ℝ)^4633 ≤ (43390857544357/100000000000000 : ℝ)^3609 := by
    have hnat : (2609225429 : ℕ)^4633*100000000000000^3609 ≤ 43390857544357^3609*5000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609225429 5000000000 43390857544357 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337191717/2500000000 : ℝ), (-118450933/625000000 : ℝ), (2609225429/5000000000 : ℝ)] ![(4478676509529/10000000000000 : ℝ), (2955594336597/25000000000000 : ℝ), (43390857544357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337191717/2500000000 : ℝ)|^4633 ≤ (4478676509529/10000000000000 : ℝ)^3609
        have hw : |(1337191717/2500000000 : ℝ)|=(1337191717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-118450933/625000000 : ℝ)|^4633 ≤ (2955594336597/25000000000000 : ℝ)^3609
        have hw : |(-118450933/625000000 : ℝ)|=(118450933/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609225429/5000000000 : ℝ)|^4633 ≤ (43390857544357/100000000000000 : ℝ)^3609
        have hw : |(2609225429/5000000000 : ℝ)|=(2609225429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s3_2 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348766447/10000000000 : ℝ)*x 0 + (1043690211/2000000000 : ℝ)*x 1 + (-1895215231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348766447/10000000000 : ℝ)^4633 ≤ (22393380284963/50000000000000 : ℝ)^3609 := by
    have hnat : (5348766447 : ℕ)^4633*50000000000000^3609 ≤ 22393380284963^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348766447 10000000000 22393380284963 50000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043690211/2000000000 : ℝ)^4633 ≤ (43390859647159/100000000000000 : ℝ)^3609 := by
    have hnat : (1043690211 : ℕ)^4633*100000000000000^3609 ≤ 43390859647159^3609*2000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043690211 2000000000 43390859647159 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1895215231/10000000000 : ℝ)^4633 ≤ (11822379772799/100000000000000 : ℝ)^3609 := by
    have hnat : (1895215231 : ℕ)^4633*100000000000000^3609 ≤ 11822379772799^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1895215231 10000000000 11822379772799 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348766447/10000000000 : ℝ), (1043690211/2000000000 : ℝ), (-1895215231/10000000000 : ℝ)] ![(22393380284963/50000000000000 : ℝ), (43390859647159/100000000000000 : ℝ), (11822379772799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348766447/10000000000 : ℝ)|^4633 ≤ (22393380284963/50000000000000 : ℝ)^3609
        have hw : |(5348766447/10000000000 : ℝ)|=(5348766447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043690211/2000000000 : ℝ)|^4633 ≤ (43390859647159/100000000000000 : ℝ)^3609
        have hw : |(1043690211/2000000000 : ℝ)|=(1043690211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1895215231/10000000000 : ℝ)|^4633 ≤ (11822379772799/100000000000000 : ℝ)^3609
        have hw : |(-1895215231/10000000000 : ℝ)|=(1895215231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s3_3 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (169769041/400000000 : ℝ)*x 0 + (4003338389/10000000000 : ℝ)*x 1 + (2248372241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (169769041/400000000 : ℝ)^4633 ≤ (1040020487473/3125000000000 : ℝ)^3609 := by
    have hnat : (169769041 : ℕ)^4633*3125000000000^3609 ≤ 1040020487473^3609*400000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169769041 400000000 1040020487473 3125000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4003338389/10000000000 : ℝ)^4633 ≤ (30875610267497/100000000000000 : ℝ)^3609 := by
    have hnat : (4003338389 : ℕ)^4633*100000000000000^3609 ≤ 30875610267497^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4003338389 10000000000 30875610267497 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2248372241/5000000000 : ℝ)^4633 ≤ (179218670571/500000000000 : ℝ)^3609 := by
    have hnat : (2248372241 : ℕ)^4633*500000000000^3609 ≤ 179218670571^3609*5000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248372241 5000000000 179218670571 500000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(169769041/400000000 : ℝ), (4003338389/10000000000 : ℝ), (2248372241/5000000000 : ℝ)] ![(1040020487473/3125000000000 : ℝ), (30875610267497/100000000000000 : ℝ), (179218670571/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(169769041/400000000 : ℝ)|^4633 ≤ (1040020487473/3125000000000 : ℝ)^3609
        have hw : |(169769041/400000000 : ℝ)|=(169769041/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4003338389/10000000000 : ℝ)|^4633 ≤ (30875610267497/100000000000000 : ℝ)^3609
        have hw : |(4003338389/10000000000 : ℝ)|=(4003338389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2248372241/5000000000 : ℝ)|^4633 ≤ (179218670571/500000000000 : ℝ)^3609
        have hw : |(2248372241/5000000000 : ℝ)|=(2248372241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s3_4 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-894061721/5000000000 : ℝ)*x 0 + (326222349/625000000 : ℝ)*x 1 + (1356660297/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (894061721/5000000000 : ℝ)^4633 ≤ (2742940768021/25000000000000 : ℝ)^3609 := by
    have hnat : (894061721 : ℕ)^4633*25000000000000^3609 ≤ 2742940768021^3609*5000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894061721 5000000000 2742940768021 25000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (326222349/625000000 : ℝ)^4633 ≤ (43402671225151/100000000000000 : ℝ)^3609 := by
    have hnat : (326222349 : ℕ)^4633*100000000000000^3609 ≤ 43402671225151^3609*625000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326222349 625000000 43402671225151 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356660297/2500000000 : ℝ)^4633 ≤ (45625565682589/100000000000000 : ℝ)^3609 := by
    have hnat : (1356660297 : ℕ)^4633*100000000000000^3609 ≤ 45625565682589^3609*2500000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356660297 2500000000 45625565682589 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-894061721/5000000000 : ℝ), (326222349/625000000 : ℝ), (1356660297/2500000000 : ℝ)] ![(2742940768021/25000000000000 : ℝ), (43402671225151/100000000000000 : ℝ), (45625565682589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-894061721/5000000000 : ℝ)|^4633 ≤ (2742940768021/25000000000000 : ℝ)^3609
        have hw : |(-894061721/5000000000 : ℝ)|=(894061721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(326222349/625000000 : ℝ)|^4633 ≤ (43402671225151/100000000000000 : ℝ)^3609
        have hw : |(326222349/625000000 : ℝ)|=(326222349/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356660297/2500000000 : ℝ)|^4633 ≤ (45625565682589/100000000000000 : ℝ)^3609
        have hw : |(1356660297/2500000000 : ℝ)|=(1356660297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s3_5 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293403729/10000000000 : ℝ)*x 0 + (-1687024751/10000000000 : ℝ)*x 1 + (5426641159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293403729/10000000000 : ℝ)^4633 ≤ (11048134527801/25000000000000 : ℝ)^3609 := by
    have hnat : (5293403729 : ℕ)^4633*25000000000000^3609 ≤ 11048134527801^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293403729 10000000000 11048134527801 25000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1687024751/10000000000 : ℝ)^4633 ≤ (5090948246033/50000000000000 : ℝ)^3609 := by
    have hnat : (1687024751 : ℕ)^4633*50000000000000^3609 ≤ 5090948246033^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1687024751 10000000000 5090948246033 50000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426641159/10000000000 : ℝ)^4633 ≤ (2851597835599/6250000000000 : ℝ)^3609 := by
    have hnat : (5426641159 : ℕ)^4633*6250000000000^3609 ≤ 2851597835599^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426641159 10000000000 2851597835599 6250000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293403729/10000000000 : ℝ), (-1687024751/10000000000 : ℝ), (5426641159/10000000000 : ℝ)] ![(11048134527801/25000000000000 : ℝ), (5090948246033/50000000000000 : ℝ), (2851597835599/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293403729/10000000000 : ℝ)|^4633 ≤ (11048134527801/25000000000000 : ℝ)^3609
        have hw : |(5293403729/10000000000 : ℝ)|=(5293403729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1687024751/10000000000 : ℝ)|^4633 ≤ (5090948246033/50000000000000 : ℝ)^3609
        have hw : |(-1687024751/10000000000 : ℝ)|=(1687024751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426641159/10000000000 : ℝ)|^4633 ≤ (2851597835599/6250000000000 : ℝ)^3609
        have hw : |(5426641159/10000000000 : ℝ)|=(5426641159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s3_6 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058680747/2000000000 : ℝ)*x 0 + (5426641191/10000000000 : ℝ)*x 1 + (-1687024699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058680747/2000000000 : ℝ)^4633 ≤ (11048134543877/25000000000000 : ℝ)^3609 := by
    have hnat : (1058680747 : ℕ)^4633*25000000000000^3609 ≤ 11048134543877^3609*2000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058680747 2000000000 11048134543877 25000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5426641191/10000000000 : ℝ)^4633 ≤ (45625565714969/100000000000000 : ℝ)^3609 := by
    have hnat : (5426641191 : ℕ)^4633*100000000000000^3609 ≤ 45625565714969^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426641191 10000000000 45625565714969 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1687024699/10000000000 : ℝ)^4633 ≤ (10181896089177/100000000000000 : ℝ)^3609 := by
    have hnat : (1687024699 : ℕ)^4633*100000000000000^3609 ≤ 10181896089177^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1687024699 10000000000 10181896089177 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058680747/2000000000 : ℝ), (5426641191/10000000000 : ℝ), (-1687024699/10000000000 : ℝ)] ![(11048134543877/25000000000000 : ℝ), (45625565714969/100000000000000 : ℝ), (10181896089177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058680747/2000000000 : ℝ)|^4633 ≤ (11048134543877/25000000000000 : ℝ)^3609
        have hw : |(1058680747/2000000000 : ℝ)|=(1058680747/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5426641191/10000000000 : ℝ)|^4633 ≤ (45625565714969/100000000000000 : ℝ)^3609
        have hw : |(5426641191/10000000000 : ℝ)|=(5426641191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1687024699/10000000000 : ℝ)|^4633 ≤ (10181896089177/100000000000000 : ℝ)^3609
        have hw : |(-1687024699/10000000000 : ℝ)|=(1687024699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s3_7 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (424429209/1000000000 : ℝ)*x 0 + (4494135153/10000000000 : ℝ)*x 1 + (1001491891/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (424429209/1000000000 : ℝ)^4633 ≤ (33281320629057/100000000000000 : ℝ)^3609 := by
    have hnat : (424429209 : ℕ)^4633*100000000000000^3609 ≤ 33281320629057^3609*1000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424429209 1000000000 33281320629057 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4494135153/10000000000 : ℝ)^4633 ≤ (35817035818573/100000000000000 : ℝ)^3609 := by
    have hnat : (4494135153 : ℕ)^4633*100000000000000^3609 ≤ 35817035818573^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494135153 10000000000 35817035818573 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1001491891/2500000000 : ℝ)^4633 ≤ (30901643531153/100000000000000 : ℝ)^3609 := by
    have hnat : (1001491891 : ℕ)^4633*100000000000000^3609 ≤ 30901643531153^3609*2500000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001491891 2500000000 30901643531153 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(424429209/1000000000 : ℝ), (4494135153/10000000000 : ℝ), (1001491891/2500000000 : ℝ)] ![(33281320629057/100000000000000 : ℝ), (35817035818573/100000000000000 : ℝ), (30901643531153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(424429209/1000000000 : ℝ)|^4633 ≤ (33281320629057/100000000000000 : ℝ)^3609
        have hw : |(424429209/1000000000 : ℝ)|=(424429209/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4494135153/10000000000 : ℝ)|^4633 ≤ (35817035818573/100000000000000 : ℝ)^3609
        have hw : |(4494135153/10000000000 : ℝ)|=(4494135153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1001491891/2500000000 : ℝ)|^4633 ≤ (30901643531153/100000000000000 : ℝ)^3609
        have hw : |(1001491891/2500000000 : ℝ)|=(1001491891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1568_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167867307/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15817/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1351/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (5541/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (97/625 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15817/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1351/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15817/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1351/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15817/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1351/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15817/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1351/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15817/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1351/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15817/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1351/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1351/12500 : ℝ) ^ (4631/1024 : ℝ) ≤ (4267278881559113/100000000000000000000 : ℝ) := by
    have hpowers : (1351/12500 : ℝ)^4631 ≤ (4267278881559113/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1351 : ℕ)^4631*100000000000000000000^1024 ≤ 4267278881559113^1024*12500^4631 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1351 12500 4267278881559113 100000000000000000000 4631 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1351/12500 : ℝ)) (X := (4267278881559113/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4631 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15817/100000 : ℝ) ^ (4631/1024 : ℝ) ≤ (11940983464192093/50000000000000000000 : ℝ) := by
    have hpowers : (15817/100000 : ℝ)^4631 ≤ (11940983464192093/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15817 : ℕ)^4631*50000000000000000000^1024 ≤ 11940983464192093^1024*100000^4631 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15817 100000 11940983464192093 50000000000000000000 4631 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15817/100000 : ℝ)) (X := (11940983464192093/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4631 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004267278881559113/50000000000000000000 : ℝ) ≤ (10000188708630809/10000000000000000 : ℝ) ^ (4631/1024 : ℝ) := by
    have hpowers : (50004267278881559113/50000000000000000000 : ℝ)^1024 ≤ (10000188708630809/10000000000000000 : ℝ)^4631 := by
      have hnat : (50004267278881559113 : ℕ)^1024*10000000000000000^4631 ≤ 10000188708630809^4631*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004267278881559113 50000000000000000000 10000188708630809 10000000000000000 1024 4631 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000188708630809/10000000000000000 : ℝ)) (X := (50004267278881559113/50000000000000000000 : ℝ)) (by norm_num) 4631 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100028149245809943299/100000000000000000000 : ℝ) ≤ (10000622363816147/10000000000000000 : ℝ) ^ (4631/1024 : ℝ) := by
    have hpowers : (100028149245809943299/100000000000000000000 : ℝ)^1024 ≤ (10000622363816147/10000000000000000 : ℝ)^4631 := by
      have hnat : (100028149245809943299 : ℕ)^1024*10000000000000000^4631 ≤ 10000622363816147^4631*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100028149245809943299 100000000000000000000 10000622363816147 10000000000000000 1024 4631 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000622363816147/10000000000000000 : ℝ)) (X := (100028149245809943299/100000000000000000000 : ℝ)) (by norm_num) 4631 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25011940983464192093/25000000000000000000 : ℝ) ≤ (2000211203800297/2000000000000000 : ℝ) ^ (4631/1024 : ℝ) := by
    have hpowers : (25011940983464192093/25000000000000000000 : ℝ)^1024 ≤ (2000211203800297/2000000000000000 : ℝ)^4631 := by
      have hnat : (25011940983464192093 : ℕ)^1024*2000000000000000^4631 ≤ 2000211203800297^4631*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011940983464192093 25000000000000000000 2000211203800297 2000000000000000 1024 4631 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000211203800297/2000000000000000 : ℝ)) (X := (25011940983464192093/25000000000000000000 : ℝ)) (by norm_num) 4631 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4267278881559113/100000000000000000000 : ℝ) ≤ ((50081571351045456073/50090000000000000000 : ℝ)+2*(216827592669/250450000000000 : ℝ)*(1351/12500 : ℝ))^(4631/1024 : ℝ) := by
    rw [show (50081571351045456073/50090000000000000000 : ℝ)+2*(216827592669/250450000000000 : ℝ)*(1351/12500 : ℝ)=(10000188708630809/10000000000000000 : ℝ) by norm_num, show 1+2*(4267278881559113/100000000000000000000 : ℝ)=(50004267278881559113/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11940983464192093/50000000000000000000 : ℝ)+(4267278881559113/100000000000000000000 : ℝ) ≤ ((50081571351045456073/50090000000000000000 : ℝ)+(216827592669/250450000000000 : ℝ)*((15817/100000 : ℝ)+(1351/12500 : ℝ)))^(4631/1024 : ℝ) := by
    rw [show (50081571351045456073/50090000000000000000 : ℝ)+(216827592669/250450000000000 : ℝ)*((15817/100000 : ℝ)+(1351/12500 : ℝ))=(10000622363816147/10000000000000000 : ℝ) by norm_num, show 1+(11940983464192093/50000000000000000000 : ℝ)+(4267278881559113/100000000000000000000 : ℝ)=(100028149245809943299/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11940983464192093/50000000000000000000 : ℝ) ≤ ((50081571351045456073/50090000000000000000 : ℝ)+2*(216827592669/250450000000000 : ℝ)*(15817/100000 : ℝ))^(4631/1024 : ℝ) := by
    rw [show (50081571351045456073/50090000000000000000 : ℝ)+2*(216827592669/250450000000000 : ℝ)*(15817/100000 : ℝ)=(2000211203800297/2000000000000000 : ℝ) by norm_num, show 1+2*(11940983464192093/50000000000000000000 : ℝ)=(25011940983464192093/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (50081571351045456073/50090000000000000000 : ℝ)*(X 1 0+X 2 0)+(216827592669/250450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4631/1024 : ℝ)) (lo := (1351/12500 : ℝ)) (hi := (15817/100000 : ℝ)) (c := (50081571351045456073/50090000000000000000 : ℝ)) (alpha := (216827592669/250450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (50081571351045456073/50090000000000000000 : ℝ)*(X 0 1+X 2 1)+(216827592669/250450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4631/1024 : ℝ)) (lo := (1351/12500 : ℝ)) (hi := (15817/100000 : ℝ)) (c := (50081571351045456073/50090000000000000000 : ℝ)) (alpha := (216827592669/250450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (50081571351045456073/50090000000000000000 : ℝ)*(X 0 2+X 1 2)+(216827592669/250450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4631/1024 : ℝ)) (lo := (1351/12500 : ℝ)) (hi := (15817/100000 : ℝ)) (c := (50081571351045456073/50090000000000000000 : ℝ)) (alpha := (216827592669/250450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-894047663/5000000000 : ℝ)*X 0 0+(5427756351/10000000000 : ℝ)*X 0 1+(5218450723/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337191717/2500000000 : ℝ)*X 1 0+(-118450933/625000000 : ℝ)*X 1 1+(2609225429/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348766447/10000000000 : ℝ)*X 2 0+(1043690211/2000000000 : ℝ)*X 2 1+(-1895215231/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((169769041/400000000 : ℝ)*X 0 0+(4003338389/10000000000 : ℝ)*X 0 1+(2248372241/5000000000 : ℝ)*X 0 2+(169769041/400000000 : ℝ)*X 1 0+(4003338389/10000000000 : ℝ)*X 1 1+(2248372241/5000000000 : ℝ)*X 1 2+(169769041/400000000 : ℝ)*X 2 0+(4003338389/10000000000 : ℝ)*X 2 1+(2248372241/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-894061721/5000000000 : ℝ)*X 0 0+(326222349/625000000 : ℝ)*X 0 1+(1356660297/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293403729/10000000000 : ℝ)*X 1 0+(-1687024751/10000000000 : ℝ)*X 1 1+(5426641159/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058680747/2000000000 : ℝ)*X 2 0+(5426641191/10000000000 : ℝ)*X 2 1+(-1687024699/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((424429209/1000000000 : ℝ)*X 0 0+(4494135153/10000000000 : ℝ)*X 0 1+(1001491891/2500000000 : ℝ)*X 0 2+(424429209/1000000000 : ℝ)*X 1 0+(4494135153/10000000000 : ℝ)*X 1 1+(1001491891/2500000000 : ℝ)*X 1 2+(424429209/1000000000 : ℝ)*X 2 0+(4494135153/10000000000 : ℝ)*X 2 1+(1001491891/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6232638088419621592669128867/1252250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (845828189/100000000000000 : ℝ)*(base19) + (141266053/25000000000000 : ℝ)*(base23) + (265488101/100000000000000 : ℝ)*(upper3) + (26841063/50000000000000 : ℝ)*(lower4) + (3402237802625593/100000000000000 : ℝ)*(major0) + (3402237802625593/100000000000000 : ℝ)*(major1) + (3402237802625593/100000000000000 : ℝ)*(major2) + (4777723317219193/100000000000000 : ℝ)*(sp0) + (2388866121803029/50000000000000 : ℝ)*(sp1) + (59721650427551/1250000000000 : ℝ)*(sp2) + (405346880380761/20000000000000 : ℝ)*(sp3) + (4886107527/50000000000000 : ℝ)*(sp4) + (98033191/20000000000000 : ℝ)*(sp6) + (7948008077/100000000000000 : ℝ)*(sp7) + (1013371174955941/50000000000000 : ℝ)*(f.failure) + (4777733089434247/100000000000000 : ℝ)*(f.sum) + (5779424258329/25045000000000000000000000000 : ℝ)*base65 + (21035944694754523711/5009000000000000000000000000000000 : ℝ)*base68 + (3715408069929476289/5009000000000000000000000000000000 : ℝ)*base69 + (780085629500523711/5009000000000000000000000000000000 : ℝ)*base72 + (247587146461/6261250000000000000000000000 : ℝ)*base73 + (57863870838727523711/5009000000000000000000000000000000 : ℝ)*base76 + (43591304068569523711/5009000000000000000000000000000000 : ℝ)*base78 + (16731423107488523711/5009000000000000000000000000000000 : ℝ)*base80 + (164137578176849/25045000000000000000000000000 : ℝ)*base81 + (9320887/5000000000000000000000 : ℝ)*base89 + (9320887/5000000000000000000000 : ℝ)*base91 + (9320887/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (40606867345189121819889/12522500000000000000000000000 : ℝ) := by norm_num
    linear_combination (262889533/50000000000000 : ℝ)*(base19) + (539015431/100000000000000 : ℝ)*(base23) + (290043/100000000000000 : ℝ)*(upper2) + (6822247/12500000000000 : ℝ)*(upper3) + (39214007/50000000000000 : ℝ)*(upper5) + (1719361265842271/50000000000000 : ℝ)*(major0) + (1719361265842271/50000000000000 : ℝ)*(major1) + (1719361265842271/50000000000000 : ℝ)*(major2) + (4127849609/50000000000000 : ℝ)*(sp1) + (8945598949/100000000000000 : ℝ)*(sp2) + (2414484169079183/50000000000000 : ℝ)*(sp4) + (4828959556680083/100000000000000 : ℝ)*(sp5) + (2414479426771993/50000000000000 : ℝ)*(sp6) + (256059577140037/12500000000000 : ℝ)*(sp7) + (256059577140037/12500000000000 : ℝ)*(f.failure) + (2414484169079183/50000000000000 : ℝ)*(f.sum) + (6309616622983/3130625000000000000000000000 : ℝ)*base66 + (14479619663292861783/2504500000000000000000000000000000 : ℝ)*base67 + (10668677737947138217/2504500000000000000000000000000000 : ℝ)*base70 + (3369696886267361783/2504500000000000000000000000000000 : ℝ)*base71 + (102200848660901/25045000000000000000000000000 : ℝ)*base73 + (6568777259395638217/2504500000000000000000000000000000 : ℝ)*base76 + (3103717278051638217/2504500000000000000000000000000000 : ℝ)*base78 + (19675152877296361783/2504500000000000000000000000000000 : ℝ)*base79 + (118011618072799/25045000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1929641/1250000000000000000000 : ℝ)*base90 + (1929641/1250000000000000000000 : ℝ)*base92 + (1929641/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1568_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167867307/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15817/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1351/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5541/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (97/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1568_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1568_s4_0 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1788325733/10000000000 : ℝ)*x 0 + (2713104969/5000000000 : ℝ)*x 1 + (2609922171/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1788325733/10000000000 : ℝ)^4633 ≤ (10973356520003/100000000000000 : ℝ)^3609 := by
    have hnat : (1788325733 : ℕ)^4633*100000000000000^3609 ≤ 10973356520003^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1788325733 10000000000 10973356520003 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713104969/5000000000 : ℝ)^4633 ≤ (22810455571197/50000000000000 : ℝ)^3609 := by
    have hnat : (2713104969 : ℕ)^4633*50000000000000^3609 ≤ 22810455571197^3609*5000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713104969 5000000000 22810455571197 50000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609922171/5000000000 : ℝ)^4633 ≤ (4340573232229/10000000000000 : ℝ)^3609 := by
    have hnat : (2609922171 : ℕ)^4633*10000000000000^3609 ≤ 4340573232229^3609*5000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609922171 5000000000 4340573232229 10000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1788325733/10000000000 : ℝ), (2713104969/5000000000 : ℝ), (2609922171/5000000000 : ℝ)] ![(10973356520003/100000000000000 : ℝ), (22810455571197/50000000000000 : ℝ), (4340573232229/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1788325733/10000000000 : ℝ)|^4633 ≤ (10973356520003/100000000000000 : ℝ)^3609
        have hw : |(-1788325733/10000000000 : ℝ)|=(1788325733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713104969/5000000000 : ℝ)|^4633 ≤ (22810455571197/50000000000000 : ℝ)^3609
        have hw : |(2713104969/5000000000 : ℝ)|=(2713104969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609922171/5000000000 : ℝ)|^4633 ≤ (4340573232229/10000000000000 : ℝ)^3609
        have hw : |(2609922171/5000000000 : ℝ)|=(2609922171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s4_1 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348357457/10000000000 : ℝ)*x 0 + (-37878137/200000000 : ℝ)*x 1 + (5219844339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348357457/10000000000 : ℝ)^4633 ≤ (44782364349979/100000000000000 : ℝ)^3609 := by
    have hnat : (5348357457 : ℕ)^4633*100000000000000^3609 ≤ 44782364349979^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348357457 10000000000 44782364349979 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (37878137/200000000 : ℝ)^4633 ≤ (73824395869/625000000000 : ℝ)^3609 := by
    have hnat : (37878137 : ℕ)^4633*625000000000^3609 ≤ 73824395869^3609*200000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37878137 200000000 73824395869 625000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219844339/10000000000 : ℝ)^4633 ≤ (21702866145133/50000000000000 : ℝ)^3609 := by
    have hnat : (5219844339 : ℕ)^4633*50000000000000^3609 ≤ 21702866145133^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219844339 10000000000 21702866145133 50000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348357457/10000000000 : ℝ), (-37878137/200000000 : ℝ), (5219844339/10000000000 : ℝ)] ![(44782364349979/100000000000000 : ℝ), (73824395869/625000000000 : ℝ), (21702866145133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348357457/10000000000 : ℝ)|^4633 ≤ (44782364349979/100000000000000 : ℝ)^3609
        have hw : |(5348357457/10000000000 : ℝ)|=(5348357457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-37878137/200000000 : ℝ)|^4633 ≤ (73824395869/625000000000 : ℝ)^3609
        have hw : |(-37878137/200000000 : ℝ)|=(37878137/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219844339/10000000000 : ℝ)|^4633 ≤ (21702866145133/50000000000000 : ℝ)^3609
        have hw : |(5219844339/10000000000 : ℝ)|=(5219844339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s4_2 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348357459/10000000000 : ℝ)*x 0 + (5219844339/10000000000 : ℝ)*x 1 + (-1893906847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348357459/10000000000 : ℝ)^4633 ≤ (44782364371477/100000000000000 : ℝ)^3609 := by
    have hnat : (5348357459 : ℕ)^4633*100000000000000^3609 ≤ 44782364371477^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348357459 10000000000 44782364371477 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219844339/10000000000 : ℝ)^4633 ≤ (21702866145133/50000000000000 : ℝ)^3609 := by
    have hnat : (5219844339 : ℕ)^4633*50000000000000^3609 ≤ 21702866145133^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219844339 10000000000 21702866145133 50000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1893906847/10000000000 : ℝ)^4633 ≤ (11811903315021/100000000000000 : ℝ)^3609 := by
    have hnat : (1893906847 : ℕ)^4633*100000000000000^3609 ≤ 11811903315021^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1893906847 10000000000 11811903315021 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348357459/10000000000 : ℝ), (5219844339/10000000000 : ℝ), (-1893906847/10000000000 : ℝ)] ![(44782364371477/100000000000000 : ℝ), (21702866145133/50000000000000 : ℝ), (11811903315021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348357459/10000000000 : ℝ)|^4633 ≤ (44782364371477/100000000000000 : ℝ)^3609
        have hw : |(5348357459/10000000000 : ℝ)|=(5348357459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219844339/10000000000 : ℝ)|^4633 ≤ (21702866145133/50000000000000 : ℝ)^3609
        have hw : |(5219844339/10000000000 : ℝ)|=(5219844339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1893906847/10000000000 : ℝ)|^4633 ≤ (11811903315021/100000000000000 : ℝ)^3609
        have hw : |(-1893906847/10000000000 : ℝ)|=(1893906847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s4_3 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4244371689/10000000000 : ℝ)*x 0 + (4006787769/10000000000 : ℝ)*x 1 + (70207233/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4244371689/10000000000 : ℝ)^4633 ≤ (2080132618759/6250000000000 : ℝ)^3609 := by
    have hnat : (4244371689 : ℕ)^4633*6250000000000^3609 ≤ 2080132618759^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244371689 10000000000 2080132618759 6250000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4006787769/10000000000 : ℝ)^4633 ≤ (7727441483823/25000000000000 : ℝ)^3609 := by
    have hnat : (4006787769 : ℕ)^4633*25000000000000^3609 ≤ 7727441483823^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4006787769 10000000000 7727441483823 25000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (70207233/156250000 : ℝ)^4633 ≤ (35808112149247/100000000000000 : ℝ)^3609 := by
    have hnat : (70207233 : ℕ)^4633*100000000000000^3609 ≤ 35808112149247^3609*156250000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70207233 156250000 35808112149247 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4244371689/10000000000 : ℝ), (4006787769/10000000000 : ℝ), (70207233/156250000 : ℝ)] ![(2080132618759/6250000000000 : ℝ), (7727441483823/25000000000000 : ℝ), (35808112149247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4244371689/10000000000 : ℝ)|^4633 ≤ (2080132618759/6250000000000 : ℝ)^3609
        have hw : |(4244371689/10000000000 : ℝ)|=(4244371689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4006787769/10000000000 : ℝ)|^4633 ≤ (7727441483823/25000000000000 : ℝ)^3609
        have hw : |(4006787769/10000000000 : ℝ)|=(4006787769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(70207233/156250000 : ℝ)|^4633 ≤ (35808112149247/100000000000000 : ℝ)^3609
        have hw : |(70207233/156250000 : ℝ)|=(70207233/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s4_4 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-223544089/1250000000 : ℝ)*x 0 + (5220920423/10000000000 : ℝ)*x 1 + (5425125879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (223544089/1250000000 : ℝ)^4633 ≤ (137169612971/1250000000000 : ℝ)^3609 := by
    have hnat : (223544089 : ℕ)^4633*1250000000000^3609 ≤ 137169612971^3609*1250000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223544089 1250000000 137169612971 1250000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220920423/10000000000 : ℝ)^4633 ≤ (43417219745403/100000000000000 : ℝ)^3609 := by
    have hnat : (5220920423 : ℕ)^4633*100000000000000^3609 ≤ 43417219745403^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220920423 10000000000 43417219745403 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5425125879/10000000000 : ℝ)^4633 ≤ (22804605604491/50000000000000 : ℝ)^3609 := by
    have hnat : (5425125879 : ℕ)^4633*50000000000000^3609 ≤ 22804605604491^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425125879 10000000000 22804605604491 50000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-223544089/1250000000 : ℝ), (5220920423/10000000000 : ℝ), (5425125879/10000000000 : ℝ)] ![(137169612971/1250000000000 : ℝ), (43417219745403/100000000000000 : ℝ), (22804605604491/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-223544089/1250000000 : ℝ)|^4633 ≤ (137169612971/1250000000000 : ℝ)^3609
        have hw : |(-223544089/1250000000 : ℝ)|=(223544089/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220920423/10000000000 : ℝ)|^4633 ≤ (43417219745403/100000000000000 : ℝ)^3609
        have hw : |(5220920423/10000000000 : ℝ)|=(5220920423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5425125879/10000000000 : ℝ)|^4633 ≤ (22804605604491/50000000000000 : ℝ)^3609
        have hw : |(5425125879/10000000000 : ℝ)|=(5425125879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s4_5 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646886217/5000000000 : ℝ)*x 0 + (-422156327/2500000000 : ℝ)*x 1 + (2712562939/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646886217/5000000000 : ℝ)^4633 ≤ (44196489708347/100000000000000 : ℝ)^3609 := by
    have hnat : (2646886217 : ℕ)^4633*100000000000000^3609 ≤ 44196489708347^3609*5000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646886217 5000000000 44196489708347 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422156327/2500000000 : ℝ)^4633 ≤ (5097149538701/50000000000000 : ℝ)^3609 := by
    have hnat : (422156327 : ℕ)^4633*50000000000000^3609 ≤ 5097149538701^3609*2500000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422156327 2500000000 5097149538701 50000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712562939/5000000000 : ℝ)^4633 ≤ (45609211198189/100000000000000 : ℝ)^3609 := by
    have hnat : (2712562939 : ℕ)^4633*100000000000000^3609 ≤ 45609211198189^3609*5000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712562939 5000000000 45609211198189 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646886217/5000000000 : ℝ), (-422156327/2500000000 : ℝ), (2712562939/5000000000 : ℝ)] ![(44196489708347/100000000000000 : ℝ), (5097149538701/50000000000000 : ℝ), (45609211198189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646886217/5000000000 : ℝ)|^4633 ≤ (44196489708347/100000000000000 : ℝ)^3609
        have hw : |(2646886217/5000000000 : ℝ)|=(2646886217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-422156327/2500000000 : ℝ)|^4633 ≤ (5097149538701/50000000000000 : ℝ)^3609
        have hw : |(-422156327/2500000000 : ℝ)|=(422156327/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712562939/5000000000 : ℝ)|^4633 ≤ (45609211198189/100000000000000 : ℝ)^3609
        have hw : |(2712562939/5000000000 : ℝ)|=(2712562939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s4_6 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293772441/10000000000 : ℝ)*x 0 + (339070367/625000000 : ℝ)*x 1 + (-1688625307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293772441/10000000000 : ℝ)^4633 ≤ (44196489783371/100000000000000 : ℝ)^3609 := by
    have hnat : (5293772441 : ℕ)^4633*100000000000000^3609 ≤ 44196489783371^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293772441 10000000000 44196489783371 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339070367/625000000 : ℝ)^4633 ≤ (9121842226687/20000000000000 : ℝ)^3609 := by
    have hnat : (339070367 : ℕ)^4633*20000000000000^3609 ≤ 9121842226687^3609*625000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339070367 625000000 9121842226687 20000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1688625307/10000000000 : ℝ)^4633 ≤ (2548574767413/25000000000000 : ℝ)^3609 := by
    have hnat : (1688625307 : ℕ)^4633*25000000000000^3609 ≤ 2548574767413^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1688625307 10000000000 2548574767413 25000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293772441/10000000000 : ℝ), (339070367/625000000 : ℝ), (-1688625307/10000000000 : ℝ)] ![(44196489783371/100000000000000 : ℝ), (9121842226687/20000000000000 : ℝ), (2548574767413/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293772441/10000000000 : ℝ)|^4633 ≤ (44196489783371/100000000000000 : ℝ)^3609
        have hw : |(5293772441/10000000000 : ℝ)|=(5293772441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339070367/625000000 : ℝ)|^4633 ≤ (9121842226687/20000000000000 : ℝ)^3609
        have hw : |(339070367/625000000 : ℝ)|=(339070367/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1688625307/10000000000 : ℝ)|^4633 ≤ (2548574767413/25000000000000 : ℝ)^3609
        have hw : |(-1688625307/10000000000 : ℝ)|=(1688625307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s4_7 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4244435249/10000000000 : ℝ)*x 0 + (2245363089/5000000000 : ℝ)*x 1 + (2004671643/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4244435249/10000000000 : ℝ)^4633 ≤ (33282761720167/100000000000000 : ℝ)^3609 := by
    have hnat : (4244435249 : ℕ)^4633*100000000000000^3609 ≤ 33282761720167^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244435249 10000000000 33282761720167 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2245363089/5000000000 : ℝ)^4633 ≤ (35782162281319/100000000000000 : ℝ)^3609 := by
    have hnat : (2245363089 : ℕ)^4633*100000000000000^3609 ≤ 35782162281319^3609*5000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245363089 5000000000 35782162281319 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2004671643/5000000000 : ℝ)^4633 ≤ (15467537988413/50000000000000 : ℝ)^3609 := by
    have hnat : (2004671643 : ℕ)^4633*50000000000000^3609 ≤ 15467537988413^3609*5000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004671643 5000000000 15467537988413 50000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4244435249/10000000000 : ℝ), (2245363089/5000000000 : ℝ), (2004671643/5000000000 : ℝ)] ![(33282761720167/100000000000000 : ℝ), (35782162281319/100000000000000 : ℝ), (15467537988413/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4244435249/10000000000 : ℝ)|^4633 ≤ (33282761720167/100000000000000 : ℝ)^3609
        have hw : |(4244435249/10000000000 : ℝ)|=(4244435249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2245363089/5000000000 : ℝ)|^4633 ≤ (35782162281319/100000000000000 : ℝ)^3609
        have hw : |(2245363089/5000000000 : ℝ)|=(2245363089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2004671643/5000000000 : ℝ)|^4633 ≤ (15467537988413/50000000000000 : ℝ)^3609
        have hw : |(2004671643/5000000000 : ℝ)|=(2004671643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1568_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167867307/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (97/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5541/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1389/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (484/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (97/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5541/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (97/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5541/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (97/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5541/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (97/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5541/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (97/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5541/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (97/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5541/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5541/50000 : ℝ) ^ (4631/1024 : ℝ) ≤ (2389422167234433/50000000000000000000 : ℝ) := by
    have hpowers : (5541/50000 : ℝ)^4631 ≤ (2389422167234433/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5541 : ℕ)^4631*50000000000000000000^1024 ≤ 2389422167234433^1024*50000^4631 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5541 50000 2389422167234433 50000000000000000000 4631 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5541/50000 : ℝ)) (X := (2389422167234433/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4631 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (97/625 : ℝ) ^ (4631/1024 : ℝ) ≤ (1095997087126647/5000000000000000000 : ℝ) := by
    have hpowers : (97/625 : ℝ)^4631 ≤ (1095997087126647/5000000000000000000 : ℝ)^1024 := by
      have hnat : (97 : ℕ)^4631*5000000000000000000^1024 ≤ 1095997087126647^1024*625^4631 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        97 625 1095997087126647 5000000000000000000 4631 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (97/625 : ℝ)) (X := (1095997087126647/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4631 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002389422167234433/25000000000000000000 : ℝ) ≤ (5000105665179527/5000000000000000 : ℝ) ^ (4631/1024 : ℝ) := by
    have hpowers : (25002389422167234433/25000000000000000000 : ℝ)^1024 ≤ (5000105665179527/5000000000000000 : ℝ)^4631 := by
      have hnat : (25002389422167234433 : ℕ)^1024*5000000000000000^4631 ≤ 5000105665179527^4631*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002389422167234433 25000000000000000000 5000105665179527 5000000000000000 1024 4631 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000105665179527/5000000000000000 : ℝ)) (X := (25002389422167234433/25000000000000000000 : ℝ)) (by norm_num) 4631 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50013349393038500903/50000000000000000000 : ℝ) ≤ (10000590298310009/10000000000000000 : ℝ) ^ (4631/1024 : ℝ) := by
    have hpowers : (50013349393038500903/50000000000000000000 : ℝ)^1024 ≤ (10000590298310009/10000000000000000 : ℝ)^4631 := by
      have hnat : (50013349393038500903 : ℕ)^1024*10000000000000000^4631 ≤ 10000590298310009^4631*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013349393038500903 50000000000000000000 10000590298310009 10000000000000000 1024 4631 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000590298310009/10000000000000000 : ℝ)) (X := (50013349393038500903/50000000000000000000 : ℝ)) (by norm_num) 4631 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501095997087126647/2500000000000000000 : ℝ) ≤ (2500242316565241/2500000000000000 : ℝ) ^ (4631/1024 : ℝ) := by
    have hpowers : (2501095997087126647/2500000000000000000 : ℝ)^1024 ≤ (2500242316565241/2500000000000000 : ℝ)^4631 := by
      have hnat : (2501095997087126647 : ℕ)^1024*2500000000000000^4631 ≤ 2500242316565241^4631*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501095997087126647 2500000000000000000 2500242316565241 2500000000000000 1024 4631 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500242316565241/2500000000000000 : ℝ)) (X := (2501095997087126647/2500000000000000000 : ℝ)) (by norm_num) 4631 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2389422167234433/50000000000000000000 : ℝ) ≤ ((5546567304808564379/5547500000000000000 : ℝ)+2*(75793590191/88760000000000 : ℝ)*(5541/50000 : ℝ))^(4631/1024 : ℝ) := by
    rw [show (5546567304808564379/5547500000000000000 : ℝ)+2*(75793590191/88760000000000 : ℝ)*(5541/50000 : ℝ)=(5000105665179527/5000000000000000 : ℝ) by norm_num, show 1+2*(2389422167234433/50000000000000000000 : ℝ)=(25002389422167234433/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1095997087126647/5000000000000000000 : ℝ)+(2389422167234433/50000000000000000000 : ℝ) ≤ ((5546567304808564379/5547500000000000000 : ℝ)+(75793590191/88760000000000 : ℝ)*((97/625 : ℝ)+(5541/50000 : ℝ)))^(4631/1024 : ℝ) := by
    rw [show (5546567304808564379/5547500000000000000 : ℝ)+(75793590191/88760000000000 : ℝ)*((97/625 : ℝ)+(5541/50000 : ℝ))=(10000590298310009/10000000000000000 : ℝ) by norm_num, show 1+(1095997087126647/5000000000000000000 : ℝ)+(2389422167234433/50000000000000000000 : ℝ)=(50013349393038500903/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1095997087126647/5000000000000000000 : ℝ) ≤ ((5546567304808564379/5547500000000000000 : ℝ)+2*(75793590191/88760000000000 : ℝ)*(97/625 : ℝ))^(4631/1024 : ℝ) := by
    rw [show (5546567304808564379/5547500000000000000 : ℝ)+2*(75793590191/88760000000000 : ℝ)*(97/625 : ℝ)=(2500242316565241/2500000000000000 : ℝ) by norm_num, show 1+2*(1095997087126647/5000000000000000000 : ℝ)=(2501095997087126647/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5546567304808564379/5547500000000000000 : ℝ)*(X 1 0+X 2 0)+(75793590191/88760000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4631/1024 : ℝ)) (lo := (5541/50000 : ℝ)) (hi := (97/625 : ℝ)) (c := (5546567304808564379/5547500000000000000 : ℝ)) (alpha := (75793590191/88760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5546567304808564379/5547500000000000000 : ℝ)*(X 0 1+X 2 1)+(75793590191/88760000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4631/1024 : ℝ)) (lo := (5541/50000 : ℝ)) (hi := (97/625 : ℝ)) (c := (5546567304808564379/5547500000000000000 : ℝ)) (alpha := (75793590191/88760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5546567304808564379/5547500000000000000 : ℝ)*(X 0 2+X 1 2)+(75793590191/88760000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4631/1024 : ℝ)) (lo := (5541/50000 : ℝ)) (hi := (97/625 : ℝ)) (c := (5546567304808564379/5547500000000000000 : ℝ)) (alpha := (75793590191/88760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1788325733/10000000000 : ℝ)*X 0 0+(2713104969/5000000000 : ℝ)*X 0 1+(2609922171/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348357457/10000000000 : ℝ)*X 1 0+(-37878137/200000000 : ℝ)*X 1 1+(5219844339/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348357459/10000000000 : ℝ)*X 2 0+(5219844339/10000000000 : ℝ)*X 2 1+(-1893906847/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4244371689/10000000000 : ℝ)*X 0 0+(4006787769/10000000000 : ℝ)*X 0 1+(70207233/156250000 : ℝ)*X 0 2+(4244371689/10000000000 : ℝ)*X 1 0+(4006787769/10000000000 : ℝ)*X 1 1+(70207233/156250000 : ℝ)*X 1 2+(4244371689/10000000000 : ℝ)*X 2 0+(4006787769/10000000000 : ℝ)*X 2 1+(70207233/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-223544089/1250000000 : ℝ)*X 0 0+(5220920423/10000000000 : ℝ)*X 0 1+(5425125879/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2646886217/5000000000 : ℝ)*X 1 0+(-422156327/2500000000 : ℝ)*X 1 1+(2712562939/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293772441/10000000000 : ℝ)*X 2 0+(339070367/625000000 : ℝ)*X 2 1+(-1688625307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4244435249/10000000000 : ℝ)*X 0 0+(2245363089/5000000000 : ℝ)*X 0 1+(2004671643/5000000000 : ℝ)*X 0 2+(4244435249/10000000000 : ℝ)*X 1 0+(2245363089/5000000000 : ℝ)*X 1 1+(2004671643/5000000000 : ℝ)*X 1 2+(4244435249/10000000000 : ℝ)*X 2 0+(2245363089/5000000000 : ℝ)*X 2 1+(2004671643/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3689335779731486076477/1109500000000000000000000000 : ℝ) := by norm_num
    linear_combination (566333591/100000000000000 : ℝ)*(base19) + (264175007/50000000000000 : ℝ)*(base23) + (5321033/25000000000000 : ℝ)*(lower2) + (5105657/6250000000000 : ℝ)*(upper3) + (351223/625000000000 : ℝ)*(upper5) + (862674876430383/25000000000000 : ℝ)*(major0) + (862674876430383/25000000000000 : ℝ)*(major1) + (862674876430383/25000000000000 : ℝ)*(major2) + (1211444589907161/25000000000000 : ℝ)*(sp0) + (2422893465300587/50000000000000 : ℝ)*(sp1) + (4845786968584751/100000000000000 : ℝ)*(sp2) + (2055607220099507/100000000000000 : ℝ)*(sp3) + (228432653/2500000000000 : ℝ)*(sp4) + (4183567993/100000000000000 : ℝ)*(sp7) + (822244561467/40000000000 : ℝ)*(f.failure) + (1211446874233691/25000000000000 : ℝ)*(f.sum) + (4142304560017/1109500000000000000000000000 : ℝ)*base65 + (248591239832252157/138687500000000000000000000000000 : ℝ)*base67 + (198228588246064657/138687500000000000000000000000000 : ℝ)*base69 + (716229076589685343/138687500000000000000000000000000 : ℝ)*base72 + (12109810858903/2219000000000000000000000000 : ℝ)*base73 + (280187040089689657/138687500000000000000000000000000 : ℝ)*base75 + (886627916016497843/138687500000000000000000000000000 : ℝ)*base78 + (330556908841685343/138687500000000000000000000000000 : ℝ)*base80 + (945954072891/2219000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (20631/4000000000000000000 : ℝ)*base90 + (20631/4000000000000000000 : ℝ)*base92 + (20631/4000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26513293113354436989614109/3962500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1082474331/100000000000000 : ℝ)*(base19) + (1160819209/100000000000000 : ℝ)*(base23) + (68769921/50000000000000 : ℝ)*(upper3) + (8323373/25000000000000 : ℝ)*(lower4) + (146046503/100000000000000 : ℝ)*(upper5) + (348718844263767/10000000000000 : ℝ)*(major0) + (348718844263767/10000000000000 : ℝ)*(major1) + (348718844263767/10000000000000 : ℝ)*(major2) + (8699974637/50000000000000 : ℝ)*(sp1) + (2283828327/12500000000000 : ℝ)*(sp2) + (2448514242353799/50000000000000 : ℝ)*(sp4) + (4897010002283993/100000000000000 : ℝ)*(sp5) + (4897009053261773/100000000000000 : ℝ)*(sp6) + (519337044383167/25000000000000 : ℝ)*(sp7) + (519337044383167/25000000000000 : ℝ)*(f.failure) + (2448514242353799/50000000000000 : ℝ)*(f.sum) + (9352680461721/2219000000000000000000000000 : ℝ)*base65 + (269380268622568193/55475000000000000000000000000000 : ℝ)*base67 + (330827771917368193/55475000000000000000000000000000 : ℝ)*base69 + (509285087391918193/55475000000000000000000000000000 : ℝ)*base71 + (505561466689/443800000000000000000000000 : ℝ)*base73 + (849640950530818193/55475000000000000000000000000000 : ℝ)*base75 + (112569967564843193/55475000000000000000000000000000 : ℝ)*base77 + (234999974327718193/55475000000000000000000000000000 : ℝ)*base79 + (881478164123/221900000000000000000000000 : ℝ)*base82 + (29578731/2500000000000000000000 : ℝ)*base90 + (29578731/2500000000000000000000 : ℝ)*base92 + (29578731/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1568_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167867307/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (97/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5541/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1389/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (484/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1568_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1568_s5_0 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-894174251/5000000000 : ℝ)*x 0 + (108521061/200000000 : ℝ)*x 1 + (2609993081/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (894174251/5000000000 : ℝ)^4633 ≤ (10973535874811/100000000000000 : ℝ)^3609 := by
    have hnat : (894174251 : ℕ)^4633*100000000000000^3609 ≤ 10973535874811^3609*5000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894174251 5000000000 10973535874811 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108521061/200000000 : ℝ)^4633 ≤ (45619217854803/100000000000000 : ℝ)^3609 := by
    have hnat : (108521061 : ℕ)^4633*100000000000000^3609 ≤ 45619217854803^3609*200000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108521061 200000000 45619217854803 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609993081/5000000000 : ℝ)^4633 ≤ (10851811561603/25000000000000 : ℝ)^3609 := by
    have hnat : (2609993081 : ℕ)^4633*25000000000000^3609 ≤ 10851811561603^3609*5000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609993081 5000000000 10851811561603 25000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-894174251/5000000000 : ℝ), (108521061/200000000 : ℝ), (2609993081/5000000000 : ℝ)] ![(10973535874811/100000000000000 : ℝ), (45619217854803/100000000000000 : ℝ), (10851811561603/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-894174251/5000000000 : ℝ)|^4633 ≤ (10973535874811/100000000000000 : ℝ)^3609
        have hw : |(-894174251/5000000000 : ℝ)|=(894174251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108521061/200000000 : ℝ)|^4633 ≤ (45619217854803/100000000000000 : ℝ)^3609
        have hw : |(108521061/200000000 : ℝ)|=(108521061/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609993081/5000000000 : ℝ)|^4633 ≤ (10851811561603/25000000000000 : ℝ)^3609
        have hw : |(2609993081/5000000000 : ℝ)|=(2609993081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s5_1 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674158031/5000000000 : ℝ)*x 0 + (-189377333/1000000000 : ℝ)*x 1 + (2609993081/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674158031/5000000000 : ℝ)^4633 ≤ (44781919401813/100000000000000 : ℝ)^3609 := by
    have hnat : (2674158031 : ℕ)^4633*100000000000000^3609 ≤ 44781919401813^3609*5000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674158031 5000000000 44781919401813 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (189377333/1000000000 : ℝ)^4633 ≤ (11810834336671/100000000000000 : ℝ)^3609 := by
    have hnat : (189377333 : ℕ)^4633*100000000000000^3609 ≤ 11810834336671^3609*1000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189377333 1000000000 11810834336671 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609993081/5000000000 : ℝ)^4633 ≤ (10851811561603/25000000000000 : ℝ)^3609 := by
    have hnat : (2609993081 : ℕ)^4633*25000000000000^3609 ≤ 10851811561603^3609*5000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609993081 5000000000 10851811561603 25000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674158031/5000000000 : ℝ), (-189377333/1000000000 : ℝ), (2609993081/5000000000 : ℝ)] ![(44781919401813/100000000000000 : ℝ), (11810834336671/100000000000000 : ℝ), (10851811561603/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674158031/5000000000 : ℝ)|^4633 ≤ (44781919401813/100000000000000 : ℝ)^3609
        have hw : |(2674158031/5000000000 : ℝ)|=(2674158031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-189377333/1000000000 : ℝ)|^4633 ≤ (11810834336671/100000000000000 : ℝ)^3609
        have hw : |(-189377333/1000000000 : ℝ)|=(189377333/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609993081/5000000000 : ℝ)|^4633 ≤ (10851811561603/25000000000000 : ℝ)^3609
        have hw : |(2609993081/5000000000 : ℝ)|=(2609993081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s5_2 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674158031/5000000000 : ℝ)*x 0 + (2609993081/5000000000 : ℝ)*x 1 + (-1893773331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674158031/5000000000 : ℝ)^4633 ≤ (44781919401813/100000000000000 : ℝ)^3609 := by
    have hnat : (2674158031 : ℕ)^4633*100000000000000^3609 ≤ 44781919401813^3609*5000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674158031 5000000000 44781919401813 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609993081/5000000000 : ℝ)^4633 ≤ (10851811561603/25000000000000 : ℝ)^3609 := by
    have hnat : (2609993081 : ℕ)^4633*25000000000000^3609 ≤ 10851811561603^3609*5000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609993081 5000000000 10851811561603 25000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1893773331/10000000000 : ℝ)^4633 ≤ (11810834344677/100000000000000 : ℝ)^3609 := by
    have hnat : (1893773331 : ℕ)^4633*100000000000000^3609 ≤ 11810834344677^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1893773331 10000000000 11810834344677 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674158031/5000000000 : ℝ), (2609993081/5000000000 : ℝ), (-1893773331/10000000000 : ℝ)] ![(44781919401813/100000000000000 : ℝ), (10851811561603/25000000000000 : ℝ), (11810834344677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674158031/5000000000 : ℝ)|^4633 ≤ (44781919401813/100000000000000 : ℝ)^3609
        have hw : |(2674158031/5000000000 : ℝ)|=(2674158031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609993081/5000000000 : ℝ)|^4633 ≤ (10851811561603/25000000000000 : ℝ)^3609
        have hw : |(2609993081/5000000000 : ℝ)|=(2609993081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1893773331/10000000000 : ℝ)|^4633 ≤ (11810834344677/100000000000000 : ℝ)^3609
        have hw : |(-1893773331/10000000000 : ℝ)|=(1893773331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s5_3 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4244386391/10000000000 : ℝ)*x 0 + (4007138217/10000000000 : ℝ)*x 1 + (11232273/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4244386391/10000000000 : ℝ)^4633 ≤ (1040070934251/3125000000000 : ℝ)^3609 := by
    have hnat : (4244386391 : ℕ)^4633*3125000000000^3609 ≤ 1040070934251^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244386391 10000000000 1040070934251 3125000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4007138217/10000000000 : ℝ)^4633 ≤ (7728309132239/25000000000000 : ℝ)^3609 := by
    have hnat : (4007138217 : ℕ)^4633*25000000000000^3609 ≤ 7728309132239^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4007138217 10000000000 7728309132239 25000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11232273/25000000 : ℝ)^4633 ≤ (17902246777219/50000000000000 : ℝ)^3609 := by
    have hnat : (11232273 : ℕ)^4633*50000000000000^3609 ≤ 17902246777219^3609*25000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11232273 25000000 17902246777219 50000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4244386391/10000000000 : ℝ), (4007138217/10000000000 : ℝ), (11232273/25000000 : ℝ)] ![(1040070934251/3125000000000 : ℝ), (7728309132239/25000000000000 : ℝ), (17902246777219/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4244386391/10000000000 : ℝ)|^4633 ≤ (1040070934251/3125000000000 : ℝ)^3609
        have hw : |(4244386391/10000000000 : ℝ)|=(4244386391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4007138217/10000000000 : ℝ)|^4633 ≤ (7728309132239/25000000000000 : ℝ)^3609
        have hw : |(4007138217/10000000000 : ℝ)|=(4007138217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(11232273/25000000 : ℝ)|^4633 ≤ (17902246777219/50000000000000 : ℝ)^3609
        have hw : |(11232273/25000000 : ℝ)|=(11232273/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s5_4 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1788375413/10000000000 : ℝ)*x 0 + (1305264753/2500000000 : ℝ)*x 1 + (5424972219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1788375413/10000000000 : ℝ)^4633 ≤ (5486873928803/50000000000000 : ℝ)^3609 := by
    have hnat : (1788375413 : ℕ)^4633*50000000000000^3609 ≤ 5486873928803^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1788375413 10000000000 5486873928803 50000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1305264753/2500000000 : ℝ)^4633 ≤ (43418699265097/100000000000000 : ℝ)^3609 := by
    have hnat : (1305264753 : ℕ)^4633*100000000000000^3609 ≤ 43418699265097^3609*2500000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305264753 2500000000 43418699265097 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5424972219/10000000000 : ℝ)^4633 ≤ (22803776427489/50000000000000 : ℝ)^3609 := by
    have hnat : (5424972219 : ℕ)^4633*50000000000000^3609 ≤ 22803776427489^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424972219 10000000000 22803776427489 50000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1788375413/10000000000 : ℝ), (1305264753/2500000000 : ℝ), (5424972219/10000000000 : ℝ)] ![(5486873928803/50000000000000 : ℝ), (43418699265097/100000000000000 : ℝ), (22803776427489/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1788375413/10000000000 : ℝ)|^4633 ≤ (5486873928803/50000000000000 : ℝ)^3609
        have hw : |(-1788375413/10000000000 : ℝ)|=(1788375413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1305264753/2500000000 : ℝ)|^4633 ≤ (43418699265097/100000000000000 : ℝ)^3609
        have hw : |(1305264753/2500000000 : ℝ)|=(1305264753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5424972219/10000000000 : ℝ)|^4633 ≤ (22803776427489/50000000000000 : ℝ)^3609
        have hw : |(5424972219/10000000000 : ℝ)|=(5424972219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s5_5 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646905121/5000000000 : ℝ)*x 0 + (-1688787393/10000000000 : ℝ)*x 1 + (2712485969/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646905121/5000000000 : ℝ)^4633 ≤ (5524611865017/12500000000000 : ℝ)^3609 := by
    have hnat : (2646905121 : ℕ)^4633*12500000000000^3609 ≤ 5524611865017^3609*5000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646905121 5000000000 5524611865017 12500000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1688787393/10000000000 : ℝ)^4633 ≤ (1274444405859/12500000000000 : ℝ)^3609 := by
    have hnat : (1688787393 : ℕ)^4633*12500000000000^3609 ≤ 1274444405859^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1688787393 10000000000 1274444405859 12500000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712485969/5000000000 : ℝ)^4633 ≤ (45607549822337/100000000000000 : ℝ)^3609 := by
    have hnat : (2712485969 : ℕ)^4633*100000000000000^3609 ≤ 45607549822337^3609*5000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712485969 5000000000 45607549822337 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646905121/5000000000 : ℝ), (-1688787393/10000000000 : ℝ), (2712485969/5000000000 : ℝ)] ![(5524611865017/12500000000000 : ℝ), (1274444405859/12500000000000 : ℝ), (45607549822337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646905121/5000000000 : ℝ)|^4633 ≤ (5524611865017/12500000000000 : ℝ)^3609
        have hw : |(2646905121/5000000000 : ℝ)|=(2646905121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1688787393/10000000000 : ℝ)|^4633 ≤ (1274444405859/12500000000000 : ℝ)^3609
        have hw : |(-1688787393/10000000000 : ℝ)|=(1688787393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712485969/5000000000 : ℝ)|^4633 ≤ (45607549822337/100000000000000 : ℝ)^3609
        have hw : |(2712485969/5000000000 : ℝ)|=(2712485969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s5_6 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529381011/1000000000 : ℝ)*x 0 + (1356242983/2500000000 : ℝ)*x 1 + (-1688787583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529381011/1000000000 : ℝ)^4633 ≤ (345288230511/781250000000 : ℝ)^3609 := by
    have hnat : (529381011 : ℕ)^4633*781250000000^3609 ≤ 345288230511^3609*1000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529381011 1000000000 345288230511 781250000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356242983/2500000000 : ℝ)^4633 ≤ (45607549757583/100000000000000 : ℝ)^3609 := by
    have hnat : (1356242983 : ℕ)^4633*100000000000000^3609 ≤ 45607549757583^3609*2500000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356242983 2500000000 45607549757583 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1688787583/10000000000 : ℝ)^4633 ≤ (2548889179851/25000000000000 : ℝ)^3609 := by
    have hnat : (1688787583 : ℕ)^4633*25000000000000^3609 ≤ 2548889179851^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1688787583 10000000000 2548889179851 25000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529381011/1000000000 : ℝ), (1356242983/2500000000 : ℝ), (-1688787583/10000000000 : ℝ)] ![(345288230511/781250000000 : ℝ), (45607549757583/100000000000000 : ℝ), (2548889179851/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529381011/1000000000 : ℝ)|^4633 ≤ (345288230511/781250000000 : ℝ)^3609
        have hw : |(529381011/1000000000 : ℝ)|=(529381011/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356242983/2500000000 : ℝ)|^4633 ≤ (45607549757583/100000000000000 : ℝ)^3609
        have hw : |(1356242983/2500000000 : ℝ)|=(1356242983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1688787583/10000000000 : ℝ)|^4633 ≤ (2548889179851/25000000000000 : ℝ)^3609
        have hw : |(-1688787583/10000000000 : ℝ)|=(1688787583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s5_7 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4244449661/10000000000 : ℝ)*x 0 + (2245190007/5000000000 : ℝ)*x 1 + (2004843057/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4244449661/10000000000 : ℝ)^4633 ≤ (33282906797421/100000000000000 : ℝ)^3609 := by
    have hnat : (4244449661 : ℕ)^4633*100000000000000^3609 ≤ 33282906797421^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244449661 10000000000 33282906797421 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2245190007/5000000000 : ℝ)^4633 ≤ (35778621471707/100000000000000 : ℝ)^3609 := by
    have hnat : (2245190007 : ℕ)^4633*100000000000000^3609 ≤ 35778621471707^3609*5000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245190007 5000000000 35778621471707 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2004843057/5000000000 : ℝ)^4633 ≤ (1546923586031/5000000000000 : ℝ)^3609 := by
    have hnat : (2004843057 : ℕ)^4633*5000000000000^3609 ≤ 1546923586031^3609*5000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004843057 5000000000 1546923586031 5000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4244449661/10000000000 : ℝ), (2245190007/5000000000 : ℝ), (2004843057/5000000000 : ℝ)] ![(33282906797421/100000000000000 : ℝ), (35778621471707/100000000000000 : ℝ), (1546923586031/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4244449661/10000000000 : ℝ)|^4633 ≤ (33282906797421/100000000000000 : ℝ)^3609
        have hw : |(4244449661/10000000000 : ℝ)|=(4244449661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2245190007/5000000000 : ℝ)|^4633 ≤ (35778621471707/100000000000000 : ℝ)^3609
        have hw : |(2245190007/5000000000 : ℝ)|=(2245190007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2004843057/5000000000 : ℝ)|^4633 ≤ (1546923586031/5000000000000 : ℝ)^3609
        have hw : |(2004843057/5000000000 : ℝ)|=(2004843057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1568_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167867307/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1389/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (2223/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (1389/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1389/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1389/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1389/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1389/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1389/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1389/12500 : ℝ) ^ (4631/1024 : ℝ) ≤ (1209407492835827/25000000000000000000 : ℝ) := by
    have hpowers : (1389/12500 : ℝ)^4631 ≤ (1209407492835827/25000000000000000000 : ℝ)^1024 := by
      have hnat : (1389 : ℕ)^4631*25000000000000000000^1024 ≤ 1209407492835827^1024*12500^4631 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1389 12500 1209407492835827 25000000000000000000 4631 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1389/12500 : ℝ)) (X := (1209407492835827/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4631 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (484/3125 : ℝ) ^ (4631/1024 : ℝ) ≤ (21716286659335331/100000000000000000000 : ℝ) := by
    have hpowers : (484/3125 : ℝ)^4631 ≤ (21716286659335331/100000000000000000000 : ℝ)^1024 := by
      have hnat : (484 : ℕ)^4631*100000000000000000000^1024 ≤ 21716286659335331^1024*3125^4631 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        484 3125 21716286659335331 100000000000000000000 4631 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (484/3125 : ℝ)) (X := (21716286659335331/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4631 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501209407492835827/12500000000000000000 : ℝ) ≤ (5000106964941647/5000000000000000 : ℝ) ^ (4631/1024 : ℝ) := by
    have hpowers : (12501209407492835827/12500000000000000000 : ℝ)^1024 ≤ (5000106964941647/5000000000000000 : ℝ)^4631 := by
      have hnat : (12501209407492835827 : ℕ)^1024*5000000000000000^4631 ≤ 5000106964941647^4631*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501209407492835827 12500000000000000000 5000106964941647 5000000000000000 1024 4631 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000106964941647/5000000000000000 : ℝ)) (X := (12501209407492835827/12500000000000000000 : ℝ)) (by norm_num) 4631 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100026553916630678639/100000000000000000000 : ℝ) ≤ (1250073386955251/1250000000000000 : ℝ) ^ (4631/1024 : ℝ) := by
    have hpowers : (100026553916630678639/100000000000000000000 : ℝ)^1024 ≤ (1250073386955251/1250000000000000 : ℝ)^4631 := by
      have hnat : (100026553916630678639 : ℕ)^1024*1250000000000000^4631 ≤ 1250073386955251^4631*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100026553916630678639 100000000000000000000 1250073386955251 1250000000000000 1024 4631 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250073386955251/1250000000000000 : ℝ)) (X := (100026553916630678639/100000000000000000000 : ℝ)) (by norm_num) 4631 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50021716286659335331/50000000000000000000 : ℝ) ≤ (5000480130700361/5000000000000000 : ℝ) ^ (4631/1024 : ℝ) := by
    have hpowers : (50021716286659335331/50000000000000000000 : ℝ)^1024 ≤ (5000480130700361/5000000000000000 : ℝ)^4631 := by
      have hnat : (50021716286659335331 : ℕ)^1024*5000000000000000^4631 ≤ 5000480130700361^4631*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021716286659335331 50000000000000000000 5000480130700361 5000000000000000 1024 4631 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000480130700361/5000000000000000 : ℝ)) (X := (50021716286659335331/50000000000000000000 : ℝ)) (by norm_num) 4631 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1209407492835827/25000000000000000000 : ℝ) ≤ ((2734540182584227163/2735000000000000000 : ℝ)+2*(186582879357/218800000000000 : ℝ)*(1389/12500 : ℝ))^(4631/1024 : ℝ) := by
    rw [show (2734540182584227163/2735000000000000000 : ℝ)+2*(186582879357/218800000000000 : ℝ)*(1389/12500 : ℝ)=(5000106964941647/5000000000000000 : ℝ) by norm_num, show 1+2*(1209407492835827/25000000000000000000 : ℝ)=(12501209407492835827/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21716286659335331/100000000000000000000 : ℝ)+(1209407492835827/25000000000000000000 : ℝ) ≤ ((2734540182584227163/2735000000000000000 : ℝ)+(186582879357/218800000000000 : ℝ)*((484/3125 : ℝ)+(1389/12500 : ℝ)))^(4631/1024 : ℝ) := by
    rw [show (2734540182584227163/2735000000000000000 : ℝ)+(186582879357/218800000000000 : ℝ)*((484/3125 : ℝ)+(1389/12500 : ℝ))=(1250073386955251/1250000000000000 : ℝ) by norm_num, show 1+(21716286659335331/100000000000000000000 : ℝ)+(1209407492835827/25000000000000000000 : ℝ)=(100026553916630678639/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21716286659335331/100000000000000000000 : ℝ) ≤ ((2734540182584227163/2735000000000000000 : ℝ)+2*(186582879357/218800000000000 : ℝ)*(484/3125 : ℝ))^(4631/1024 : ℝ) := by
    rw [show (2734540182584227163/2735000000000000000 : ℝ)+2*(186582879357/218800000000000 : ℝ)*(484/3125 : ℝ)=(5000480130700361/5000000000000000 : ℝ) by norm_num, show 1+2*(21716286659335331/100000000000000000000 : ℝ)=(50021716286659335331/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2734540182584227163/2735000000000000000 : ℝ)*(X 1 0+X 2 0)+(186582879357/218800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4631/1024 : ℝ)) (lo := (1389/12500 : ℝ)) (hi := (484/3125 : ℝ)) (c := (2734540182584227163/2735000000000000000 : ℝ)) (alpha := (186582879357/218800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2734540182584227163/2735000000000000000 : ℝ)*(X 0 1+X 2 1)+(186582879357/218800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4631/1024 : ℝ)) (lo := (1389/12500 : ℝ)) (hi := (484/3125 : ℝ)) (c := (2734540182584227163/2735000000000000000 : ℝ)) (alpha := (186582879357/218800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2734540182584227163/2735000000000000000 : ℝ)*(X 0 2+X 1 2)+(186582879357/218800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4631/1024 : ℝ)) (lo := (1389/12500 : ℝ)) (hi := (484/3125 : ℝ)) (c := (2734540182584227163/2735000000000000000 : ℝ)) (alpha := (186582879357/218800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-894174251/5000000000 : ℝ)*X 0 0+(108521061/200000000 : ℝ)*X 0 1+(2609993081/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674158031/5000000000 : ℝ)*X 1 0+(-189377333/1000000000 : ℝ)*X 1 1+(2609993081/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674158031/5000000000 : ℝ)*X 2 0+(2609993081/5000000000 : ℝ)*X 2 1+(-1893773331/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4244386391/10000000000 : ℝ)*X 0 0+(4007138217/10000000000 : ℝ)*X 0 1+(11232273/25000000 : ℝ)*X 0 2+(4244386391/10000000000 : ℝ)*X 1 0+(4007138217/10000000000 : ℝ)*X 1 1+(11232273/25000000 : ℝ)*X 1 2+(4244386391/10000000000 : ℝ)*X 2 0+(4007138217/10000000000 : ℝ)*X 2 1+(11232273/25000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1788375413/10000000000 : ℝ)*X 0 0+(1305264753/2500000000 : ℝ)*X 0 1+(5424972219/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2646905121/5000000000 : ℝ)*X 1 0+(-1688787393/10000000000 : ℝ)*X 1 1+(2712485969/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((529381011/1000000000 : ℝ)*X 2 0+(1356242983/2500000000 : ℝ)*X 2 1+(-1688787583/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4244449661/10000000000 : ℝ)*X 0 0+(2245190007/5000000000 : ℝ)*X 0 1+(2004843057/5000000000 : ℝ)*X 0 2+(4244449661/10000000000 : ℝ)*X 1 0+(2245190007/5000000000 : ℝ)*X 1 1+(2004843057/5000000000 : ℝ)*X 1 2+(4244449661/10000000000 : ℝ)*X 2 0+(2245190007/5000000000 : ℝ)*X 2 1+(2004843057/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (127272317891764852872993993/34187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (634806751/100000000000000 : ℝ)*(base19) + (592284373/100000000000000 : ℝ)*(base23) + (22742311/100000000000000 : ℝ)*(lower2) + (93100959/100000000000000 : ℝ)*(upper3) + (6193771/10000000000000 : ℝ)*(upper5) + (1727851616776387/50000000000000 : ℝ)*(major0) + (1727851616776387/50000000000000 : ℝ)*(major1) + (1727851616776387/50000000000000 : ℝ)*(major2) + (606600489316491/12500000000000 : ℝ)*(sp0) + (194112541631647/4000000000000 : ℝ)*(sp1) + (303300848957097/6250000000000 : ℝ)*(sp2) + (411717488386449/20000000000000 : ℝ)*(sp3) + (5130532999/50000000000000 : ℝ)*(sp4) + (4725482923/100000000000000 : ℝ)*(sp7) + (16082751307931/781250000000 : ℝ)*(f.failure) + (2426407087798963/50000000000000 : ℝ)*(f.sum) + (24420523794801/5470000000000000000000000000 : ℝ)*base66 + (134460784243362419/136750000000000000000000000000000 : ℝ)*base68 + (546353515088112419/136750000000000000000000000000000 : ℝ)*base70 + (1055336280467112419/136750000000000000000000000000000 : ℝ)*base72 + (6539635349769/5470000000000000000000000000 : ℝ)*base73 + (1187578429399112419/136750000000000000000000000000000 : ℝ)*base76 + (1315642554861612419/136750000000000000000000000000000 : ℝ)*base78 + (314679131442637581/136750000000000000000000000000000 : ℝ)*base79 + (10047775143459/5470000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (24317/78125000000000000000 : ℝ)*base89 + (24317/78125000000000000000 : ℝ)*base91 + (24317/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (321248752215644363200265109/34187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (895496487/50000000000000 : ℝ)*(base19) + (1660555881/100000000000000 : ℝ)*(base23) + (191676361/50000000000000 : ℝ)*(lower1) + (100552083/50000000000000 : ℝ)*(upper3) + (10753803/50000000000000 : ℝ)*(lower4) + (54428219/25000000000000 : ℝ)*(upper5) + (1746086285313169/50000000000000 : ℝ)*(major0) + (1746086285313169/50000000000000 : ℝ)*(major1) + (1746086285313169/50000000000000 : ℝ)*(major2) + (236904851/5000000000000 : ℝ)*(sp1) + (4904027562544869/100000000000000 : ℝ)*(sp4) + (39232168267639/800000000000 : ℝ)*(sp5) + (4904025901988987/100000000000000 : ℝ)*(sp6) + (1040158632742687/50000000000000 : ℝ)*(sp7) + (1040158632742687/50000000000000 : ℝ)*(f.failure) + (4904027562544869/100000000000000 : ℝ)*(f.sum) + (19982321821657/5470000000000000000000000000 : ℝ)*base66 + (89606160893572047/136750000000000000000000000000000 : ℝ)*base67 + (193896321693322047/136750000000000000000000000000000 : ℝ)*base69 + (144798660548572047/136750000000000000000000000000000 : ℝ)*base71 + (23320090900337/5470000000000000000000000000 : ℝ)*base74 + (821340783840072047/136750000000000000000000000000000 : ℝ)*base75 + (1349690113483572047/136750000000000000000000000000000 : ℝ)*base77 + (662697086714427953/136750000000000000000000000000000 : ℝ)*base80 + (20549538383717/5470000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (9366091/5000000000000000000000 : ℝ)*base90 + (9366091/5000000000000000000000 : ℝ)*base92 + (9366091/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1568_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167867307/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1389/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2223/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1568_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1568_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167867307/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15817/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1351/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2223/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1568_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1568_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1568_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167867307/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15817/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1351/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2223/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1568_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
