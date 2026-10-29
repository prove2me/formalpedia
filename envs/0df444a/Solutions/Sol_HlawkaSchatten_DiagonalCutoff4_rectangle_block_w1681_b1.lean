-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1681_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:32:25.88555+00:00
-- url     : https://prove2.me/submissions/5693fe1c-8815-4ecb-88a2-d3d9f5192e90

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
theorem support_rectangle_w1681_s3_0 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-762083693/5000000000 : ℝ)*x 0 + (548941091/1000000000 : ℝ)*x 1 + (5133567433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (762083693/5000000000 : ℝ)^5071 ≤ (9469301065681/100000000000000 : ℝ)^4047 := by
    have hnat : (762083693 : ℕ)^5071*100000000000000^4047 ≤ 9469301065681^4047*5000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      762083693 5000000000 9469301065681 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (548941091/1000000000 : ℝ)^5071 ≤ (47164880469229/100000000000000 : ℝ)^4047 := by
    have hnat : (548941091 : ℕ)^5071*100000000000000^4047 ≤ 47164880469229^4047*1000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548941091 1000000000 47164880469229 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5133567433/10000000000 : ℝ)^5071 ≤ (43365818451609/100000000000000 : ℝ)^4047 := by
    have hnat : (5133567433 : ℕ)^5071*100000000000000^4047 ≤ 43365818451609^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5133567433 10000000000 43365818451609 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-762083693/5000000000 : ℝ), (548941091/1000000000 : ℝ), (5133567433/10000000000 : ℝ)] ![(9469301065681/100000000000000 : ℝ), (47164880469229/100000000000000 : ℝ), (43365818451609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-762083693/5000000000 : ℝ)|^5071 ≤ (9469301065681/100000000000000 : ℝ)^4047
        have hw : |(-762083693/5000000000 : ℝ)|=(762083693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(548941091/1000000000 : ℝ)|^5071 ≤ (47164880469229/100000000000000 : ℝ)^4047
        have hw : |(548941091/1000000000 : ℝ)|=(548941091/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5133567433/10000000000 : ℝ)|^5071 ≤ (43365818451609/100000000000000 : ℝ)^4047
        have hw : |(5133567433/10000000000 : ℝ)|=(5133567433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_s3_1 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353214027/10000000000 : ℝ)*x 0 + (-341833483/2000000000 : ℝ)*x 1 + (51335673/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353214027/10000000000 : ℝ)^5071 ≤ (22851609703811/50000000000000 : ℝ)^4047 := by
    have hnat : (5353214027 : ℕ)^5071*50000000000000^4047 ≤ 22851609703811^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353214027 10000000000 22851609703811 50000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (341833483/2000000000 : ℝ)^5071 ≤ (1366370442049/12500000000000 : ℝ)^4047 := by
    have hnat : (341833483 : ℕ)^5071*12500000000000^4047 ≤ 1366370442049^4047*2000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341833483 2000000000 1366370442049 12500000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51335673/100000000 : ℝ)^5071 ≤ (43365817043811/100000000000000 : ℝ)^4047 := by
    have hnat : (51335673 : ℕ)^5071*100000000000000^4047 ≤ 43365817043811^4047*100000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51335673 100000000 43365817043811 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353214027/10000000000 : ℝ), (-341833483/2000000000 : ℝ), (51335673/100000000 : ℝ)] ![(22851609703811/50000000000000 : ℝ), (1366370442049/12500000000000 : ℝ), (43365817043811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353214027/10000000000 : ℝ)|^5071 ≤ (22851609703811/50000000000000 : ℝ)^4047
        have hw : |(5353214027/10000000000 : ℝ)|=(5353214027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-341833483/2000000000 : ℝ)|^5071 ≤ (1366370442049/12500000000000 : ℝ)^4047
        have hw : |(-341833483/2000000000 : ℝ)|=(341833483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(51335673/100000000 : ℝ)|^5071 ≤ (43365817043811/100000000000000 : ℝ)^4047
        have hw : |(51335673/100000000 : ℝ)|=(51335673/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_s3_2 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353214033/10000000000 : ℝ)*x 0 + (1026713461/2000000000 : ℝ)*x 1 + (-8545837/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353214033/10000000000 : ℝ)^5071 ≤ (714112804247/1562500000000 : ℝ)^4047 := by
    have hnat : (5353214033 : ℕ)^5071*1562500000000^4047 ≤ 714112804247^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353214033 10000000000 714112804247 1562500000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1026713461/2000000000 : ℝ)^5071 ≤ (8673163419347/20000000000000 : ℝ)^4047 := by
    have hnat : (1026713461 : ℕ)^5071*20000000000000^4047 ≤ 8673163419347^4047*2000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026713461 2000000000 8673163419347 20000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8545837/50000000 : ℝ)^5071 ≤ (5465481708093/50000000000000 : ℝ)^4047 := by
    have hnat : (8545837 : ℕ)^5071*50000000000000^4047 ≤ 5465481708093^4047*50000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8545837 50000000 5465481708093 50000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353214033/10000000000 : ℝ), (1026713461/2000000000 : ℝ), (-8545837/50000000 : ℝ)] ![(714112804247/1562500000000 : ℝ), (8673163419347/20000000000000 : ℝ), (5465481708093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353214033/10000000000 : ℝ)|^5071 ≤ (714112804247/1562500000000 : ℝ)^4047
        have hw : |(5353214033/10000000000 : ℝ)|=(5353214033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1026713461/2000000000 : ℝ)|^5071 ≤ (8673163419347/20000000000000 : ℝ)^4047
        have hw : |(1026713461/2000000000 : ℝ)|=(1026713461/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8545837/50000000 : ℝ)|^5071 ≤ (5465481708093/50000000000000 : ℝ)^4047
        have hw : |(-8545837/50000000 : ℝ)|=(8545837/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_s3_3 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (828753599/2000000000 : ℝ)*x 0 + (3681086249/10000000000 : ℝ)*x 1 + (580598507/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (828753599/2000000000 : ℝ)^5071 ≤ (33157835382401/100000000000000 : ℝ)^4047 := by
    have hnat : (828753599 : ℕ)^5071*100000000000000^4047 ≤ 33157835382401^4047*2000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828753599 2000000000 33157835382401 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3681086249/10000000000 : ℝ)^5071 ≤ (28586186956111/100000000000000 : ℝ)^4047 := by
    have hnat : (3681086249 : ℕ)^5071*100000000000000^4047 ≤ 28586186956111^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3681086249 10000000000 28586186956111 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (580598507/1250000000 : ℝ)^5071 ≤ (19127988825359/50000000000000 : ℝ)^4047 := by
    have hnat : (580598507 : ℕ)^5071*50000000000000^4047 ≤ 19127988825359^4047*1250000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      580598507 1250000000 19127988825359 50000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(828753599/2000000000 : ℝ), (3681086249/10000000000 : ℝ), (580598507/1250000000 : ℝ)] ![(33157835382401/100000000000000 : ℝ), (28586186956111/100000000000000 : ℝ), (19127988825359/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(828753599/2000000000 : ℝ)|^5071 ≤ (33157835382401/100000000000000 : ℝ)^4047
        have hw : |(828753599/2000000000 : ℝ)|=(828753599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3681086249/10000000000 : ℝ)|^5071 ≤ (28586186956111/100000000000000 : ℝ)^4047
        have hw : |(3681086249/10000000000 : ℝ)|=(3681086249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(580598507/1250000000 : ℝ)|^5071 ≤ (19127988825359/50000000000000 : ℝ)^4047
        have hw : |(580598507/1250000000 : ℝ)|=(580598507/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_s3_4 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1524335169/10000000000 : ℝ)*x 0 + (2568705023/5000000000 : ℝ)*x 1 + (2742755439/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1524335169/10000000000 : ℝ)^5071 ≤ (9470607235577/100000000000000 : ℝ)^4047 := by
    have hnat : (1524335169 : ℕ)^5071*100000000000000^4047 ≤ 9470607235577^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1524335169 10000000000 9470607235577 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2568705023/5000000000 : ℝ)^5071 ≤ (43406496157087/100000000000000 : ℝ)^4047 := by
    have hnat : (2568705023 : ℕ)^5071*100000000000000^4047 ≤ 43406496157087^4047*5000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2568705023 5000000000 43406496157087 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2742755439/5000000000 : ℝ)^5071 ≤ (47122896593379/100000000000000 : ℝ)^4047 := by
    have hnat : (2742755439 : ℕ)^5071*100000000000000^4047 ≤ 47122896593379^4047*5000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2742755439 5000000000 47122896593379 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1524335169/10000000000 : ℝ), (2568705023/5000000000 : ℝ), (2742755439/5000000000 : ℝ)] ![(9470607235577/100000000000000 : ℝ), (43406496157087/100000000000000 : ℝ), (47122896593379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1524335169/10000000000 : ℝ)|^5071 ≤ (9470607235577/100000000000000 : ℝ)^4047
        have hw : |(-1524335169/10000000000 : ℝ)|=(1524335169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2568705023/5000000000 : ℝ)|^5071 ≤ (43406496157087/100000000000000 : ℝ)^4047
        have hw : |(2568705023/5000000000 : ℝ)|=(2568705023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2742755439/5000000000 : ℝ)|^5071 ≤ (47122896593379/100000000000000 : ℝ)^4047
        have hw : |(2742755439/5000000000 : ℝ)|=(2742755439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_s3_5 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051636597/2000000000 : ℝ)*x 0 + (-1357223829/10000000000 : ℝ)*x 1 + (5485510869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051636597/2000000000 : ℝ)^5071 ≤ (11172223528029/25000000000000 : ℝ)^4047 := by
    have hnat : (1051636597 : ℕ)^5071*25000000000000^4047 ≤ 11172223528029^4047*2000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051636597 2000000000 11172223528029 25000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357223829/10000000000 : ℝ)^5071 ≤ (511763085371/6250000000000 : ℝ)^4047 := by
    have hnat : (1357223829 : ℕ)^5071*6250000000000^4047 ≤ 511763085371^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357223829 10000000000 511763085371 6250000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5485510869/10000000000 : ℝ)^5071 ≤ (23561448248251/50000000000000 : ℝ)^4047 := by
    have hnat : (5485510869 : ℕ)^5071*50000000000000^4047 ≤ 23561448248251^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5485510869 10000000000 23561448248251 50000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051636597/2000000000 : ℝ), (-1357223829/10000000000 : ℝ), (5485510869/10000000000 : ℝ)] ![(11172223528029/25000000000000 : ℝ), (511763085371/6250000000000 : ℝ), (23561448248251/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051636597/2000000000 : ℝ)|^5071 ≤ (11172223528029/25000000000000 : ℝ)^4047
        have hw : |(1051636597/2000000000 : ℝ)|=(1051636597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1357223829/10000000000 : ℝ)|^5071 ≤ (511763085371/6250000000000 : ℝ)^4047
        have hw : |(-1357223829/10000000000 : ℝ)|=(1357223829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5485510869/10000000000 : ℝ)|^5071 ≤ (23561448248251/50000000000000 : ℝ)^4047
        have hw : |(5485510869/10000000000 : ℝ)|=(5485510869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_s3_6 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5258182963/10000000000 : ℝ)*x 0 + (548551091/1000000000 : ℝ)*x 1 + (-1357223803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5258182963/10000000000 : ℝ)^5071 ≤ (4468889387783/10000000000000 : ℝ)^4047 := by
    have hnat : (5258182963 : ℕ)^5071*10000000000000^4047 ≤ 4468889387783^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258182963 10000000000 4468889387783 10000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (548551091/1000000000 : ℝ)^5071 ≤ (11780724234457/25000000000000 : ℝ)^4047 := by
    have hnat : (548551091 : ℕ)^5071*25000000000000^4047 ≤ 11780724234457^4047*1000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548551091 1000000000 11780724234457 25000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357223803/10000000000 : ℝ)^5071 ≤ (8188209169387/100000000000000 : ℝ)^4047 := by
    have hnat : (1357223803 : ℕ)^5071*100000000000000^4047 ≤ 8188209169387^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357223803 10000000000 8188209169387 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5258182963/10000000000 : ℝ), (548551091/1000000000 : ℝ), (-1357223803/10000000000 : ℝ)] ![(4468889387783/10000000000000 : ℝ), (11780724234457/25000000000000 : ℝ), (8188209169387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5258182963/10000000000 : ℝ)|^5071 ≤ (4468889387783/10000000000000 : ℝ)^4047
        have hw : |(5258182963/10000000000 : ℝ)|=(5258182963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(548551091/1000000000 : ℝ)|^5071 ≤ (11780724234457/25000000000000 : ℝ)^4047
        have hw : |(548551091/1000000000 : ℝ)|=(548551091/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1357223803/10000000000 : ℝ)|^5071 ≤ (8188209169387/100000000000000 : ℝ)^4047
        have hw : |(-1357223803/10000000000 : ℝ)|=(1357223803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_s3_7 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4144222363/10000000000 : ℝ)*x 0 + (4634381121/10000000000 : ℝ)*x 1 + (461456091/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4144222363/10000000000 : ℝ)^5071 ≤ (33162391185099/100000000000000 : ℝ)^4047 := by
    have hnat : (4144222363 : ℕ)^5071*100000000000000^4047 ≤ 33162391185099^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4144222363 10000000000 33162391185099 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4634381121/10000000000 : ℝ)^5071 ≤ (7629721010633/20000000000000 : ℝ)^4047 := by
    have hnat : (4634381121 : ℕ)^5071*20000000000000^4047 ≤ 7629721010633^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4634381121 10000000000 7629721010633 20000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (461456091/1250000000 : ℝ)^5071 ≤ (28689003740293/100000000000000 : ℝ)^4047 := by
    have hnat : (461456091 : ℕ)^5071*100000000000000^4047 ≤ 28689003740293^4047*1250000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      461456091 1250000000 28689003740293 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4144222363/10000000000 : ℝ), (4634381121/10000000000 : ℝ), (461456091/1250000000 : ℝ)] ![(33162391185099/100000000000000 : ℝ), (7629721010633/20000000000000 : ℝ), (28689003740293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4144222363/10000000000 : ℝ)|^5071 ≤ (33162391185099/100000000000000 : ℝ)^4047
        have hw : |(4144222363/10000000000 : ℝ)|=(4144222363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4634381121/10000000000 : ℝ)|^5071 ≤ (7629721010633/20000000000000 : ℝ)^4047
        have hw : |(4634381121/10000000000 : ℝ)|=(4634381121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(461456091/1250000000 : ℝ)|^5071 ≤ (28689003740293/100000000000000 : ℝ)^4047
        have hw : |(461456091/1250000000 : ℝ)|=(461456091/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1681_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (185410819/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1733/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (971/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (1217/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17299/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1733/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (971/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1733/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (971/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1733/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (971/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1733/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (971/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1733/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (971/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1733/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (971/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (971/10000 : ℝ) ^ (5063/1024 : ℝ) ≤ (982814695492357/100000000000000000000 : ℝ) := by
    have hpowers : (971/10000 : ℝ)^5063 ≤ (982814695492357/100000000000000000000 : ℝ)^1024 := by
      have hnat : (971 : ℕ)^5063*100000000000000000000^1024 ≤ 982814695492357^1024*10000^5063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        971 10000 982814695492357 100000000000000000000 5063 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (971/10000 : ℝ)) (X := (982814695492357/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5063 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1733/10000 : ℝ) ^ (5063/1024 : ℝ) ≤ (1723313848281701/10000000000000000000 : ℝ) := by
    have hpowers : (1733/10000 : ℝ)^5063 ≤ (1723313848281701/10000000000000000000 : ℝ)^1024 := by
      have hnat : (1733 : ℕ)^5063*10000000000000000000^1024 ≤ 1723313848281701^1024*10000^5063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1733 10000 1723313848281701 10000000000000000000 5063 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1733/10000 : ℝ)) (X := (1723313848281701/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5063 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000982814695492357/50000000000000000000 : ℝ) ≤ (5000019877431517/5000000000000000 : ℝ) ^ (5063/1024 : ℝ) := by
    have hpowers : (50000982814695492357/50000000000000000000 : ℝ)^1024 ≤ (5000019877431517/5000000000000000 : ℝ)^5063 := by
      have hnat : (50000982814695492357 : ℕ)^1024*5000000000000000^5063 ≤ 5000019877431517^5063*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000982814695492357 50000000000000000000 5000019877431517 5000000000000000 1024 5063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000019877431517/5000000000000000 : ℝ)) (X := (50000982814695492357/50000000000000000000 : ℝ)) (by norm_num) 5063 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100018215953178309367/100000000000000000000 : ℝ) ≤ (1000036839385521/1000000000000000 : ℝ) ^ (5063/1024 : ℝ) := by
    have hpowers : (100018215953178309367/100000000000000000000 : ℝ)^1024 ≤ (1000036839385521/1000000000000000 : ℝ)^5063 := by
      have hnat : (100018215953178309367 : ℕ)^1024*1000000000000000^5063 ≤ 1000036839385521^5063*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100018215953178309367 100000000000000000000 1000036839385521 1000000000000000 1024 5063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000036839385521/1000000000000000 : ℝ)) (X := (100018215953178309367/100000000000000000000 : ℝ)) (by norm_num) 5063 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5001723313848281701/5000000000000000000 : ℝ) ≤ (5000348516423693/5000000000000000 : ℝ) ^ (5063/1024 : ℝ) := by
    have hpowers : (5001723313848281701/5000000000000000000 : ℝ)^1024 ≤ (5000348516423693/5000000000000000 : ℝ)^5063 := by
      have hnat : (5001723313848281701 : ℕ)^1024*5000000000000000^5063 ≤ 5000348516423693^5063*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001723313848281701 5000000000000000000 5000348516423693 5000000000000000 1024 5063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000348516423693/5000000000000000 : ℝ)) (X := (5001723313848281701/5000000000000000000 : ℝ)) (by norm_num) 5063 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(982814695492357/100000000000000000000 : ℝ) ≤ ((1904848019070706529/1905000000000000000 : ℝ)+2*(20539937011/47625000000000 : ℝ)*(971/10000 : ℝ))^(5063/1024 : ℝ) := by
    rw [show (1904848019070706529/1905000000000000000 : ℝ)+2*(20539937011/47625000000000 : ℝ)*(971/10000 : ℝ)=(5000019877431517/5000000000000000 : ℝ) by norm_num, show 1+2*(982814695492357/100000000000000000000 : ℝ)=(50000982814695492357/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1723313848281701/10000000000000000000 : ℝ)+(982814695492357/100000000000000000000 : ℝ) ≤ ((1904848019070706529/1905000000000000000 : ℝ)+(20539937011/47625000000000 : ℝ)*((1733/10000 : ℝ)+(971/10000 : ℝ)))^(5063/1024 : ℝ) := by
    rw [show (1904848019070706529/1905000000000000000 : ℝ)+(20539937011/47625000000000 : ℝ)*((1733/10000 : ℝ)+(971/10000 : ℝ))=(1000036839385521/1000000000000000 : ℝ) by norm_num, show 1+(1723313848281701/10000000000000000000 : ℝ)+(982814695492357/100000000000000000000 : ℝ)=(100018215953178309367/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1723313848281701/10000000000000000000 : ℝ) ≤ ((1904848019070706529/1905000000000000000 : ℝ)+2*(20539937011/47625000000000 : ℝ)*(1733/10000 : ℝ))^(5063/1024 : ℝ) := by
    rw [show (1904848019070706529/1905000000000000000 : ℝ)+2*(20539937011/47625000000000 : ℝ)*(1733/10000 : ℝ)=(5000348516423693/5000000000000000 : ℝ) by norm_num, show 1+2*(1723313848281701/10000000000000000000 : ℝ)=(5001723313848281701/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1904848019070706529/1905000000000000000 : ℝ)*(X 1 0+X 2 0)+(20539937011/47625000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5063/1024 : ℝ)) (lo := (971/10000 : ℝ)) (hi := (1733/10000 : ℝ)) (c := (1904848019070706529/1905000000000000000 : ℝ)) (alpha := (20539937011/47625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1904848019070706529/1905000000000000000 : ℝ)*(X 0 1+X 2 1)+(20539937011/47625000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5063/1024 : ℝ)) (lo := (971/10000 : ℝ)) (hi := (1733/10000 : ℝ)) (c := (1904848019070706529/1905000000000000000 : ℝ)) (alpha := (20539937011/47625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1904848019070706529/1905000000000000000 : ℝ)*(X 0 2+X 1 2)+(20539937011/47625000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5063/1024 : ℝ)) (lo := (971/10000 : ℝ)) (hi := (1733/10000 : ℝ)) (c := (1904848019070706529/1905000000000000000 : ℝ)) (alpha := (20539937011/47625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-762083693/5000000000 : ℝ)*X 0 0+(548941091/1000000000 : ℝ)*X 0 1+(5133567433/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353214027/10000000000 : ℝ)*X 1 0+(-341833483/2000000000 : ℝ)*X 1 1+(51335673/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353214033/10000000000 : ℝ)*X 2 0+(1026713461/2000000000 : ℝ)*X 2 1+(-8545837/50000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((828753599/2000000000 : ℝ)*X 0 0+(3681086249/10000000000 : ℝ)*X 0 1+(580598507/1250000000 : ℝ)*X 0 2+(828753599/2000000000 : ℝ)*X 1 0+(3681086249/10000000000 : ℝ)*X 1 1+(580598507/1250000000 : ℝ)*X 1 2+(828753599/2000000000 : ℝ)*X 2 0+(3681086249/10000000000 : ℝ)*X 2 1+(580598507/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1524335169/10000000000 : ℝ)*X 0 0+(2568705023/5000000000 : ℝ)*X 0 1+(2742755439/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1051636597/2000000000 : ℝ)*X 1 0+(-1357223829/10000000000 : ℝ)*X 1 1+(5485510869/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5258182963/10000000000 : ℝ)*X 2 0+(548551091/1000000000 : ℝ)*X 2 1+(-1357223803/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4144222363/10000000000 : ℝ)*X 0 0+(4634381121/10000000000 : ℝ)*X 0 1+(461456091/1250000000 : ℝ)*X 0 2+(4144222363/10000000000 : ℝ)*X 1 0+(4634381121/10000000000 : ℝ)*X 1 1+(461456091/1250000000 : ℝ)*X 1 2+(4144222363/10000000000 : ℝ)*X 2 0+(4634381121/10000000000 : ℝ)*X 2 1+(461456091/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2655435492337286632763189/496093750000000000000000000000 : ℝ) := by norm_num
    linear_combination (167928539/20000000000000 : ℝ)*(base19) + (200797237/25000000000000 : ℝ)*(base23) + (21200613/100000000000000 : ℝ)*(lower2) + (129443683/100000000000000 : ℝ)*(upper3) + (109737051/100000000000000 : ℝ)*(upper5) + (30061792389541/1562500000000 : ℝ)*(major0) + (30061792389541/1562500000000 : ℝ)*(major1) + (30061792389541/1562500000000 : ℝ)*(major2) + (28102311544833/1000000000000 : ℝ)*(sp0) + (175639824055151/6250000000000 : ℝ)*(sp1) + (2810237221336163/100000000000000 : ℝ)*(sp2) + (129708521949633/12500000000000 : ℝ)*(sp3) + (687004181/10000000000000 : ℝ)*(sp4) + (1523658053/50000000000000 : ℝ)*(sp7) + (103767122291317/10000000000000 : ℝ)*(f.failure) + (2810238024525111/100000000000000 : ℝ)*(f.sum) + (4745652408311/2381250000000000000000000000 : ℝ)*base66 + (3264346374073969/496093750000000000000000000000 : ℝ)*base67 + (1168672819476063/992187500000000000000000000000 : ℝ)*base69 + (2658844511613531/496093750000000000000000000000 : ℝ)*base72 + (16332124356203/4762500000000000000000000000 : ℝ)*base73 + (2036508254273937/992187500000000000000000000000 : ℝ)*base76 + (16797112744407249/1984375000000000000000000000000 : ℝ)*base78 + (9215486469094749/1984375000000000000000000000000 : ℝ)*base80 + (3086642948957/1190625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1558623/1000000000000000000000 : ℝ)*base89 + (1558623/1000000000000000000000 : ℝ)*base91 + (1558623/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18021658292717864609616933/3968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (683192277/100000000000000 : ℝ)*(base19) + (141540823/20000000000000 : ℝ)*(base23) + (101626371/50000000000000 : ℝ)*(lower1) + (5129411/5000000000000 : ℝ)*(upper3) + (14305039/100000000000000 : ℝ)*(lower4) + (12208043/12500000000000 : ℝ)*(upper5) + (491683639488627/25000000000000 : ℝ)*(major0) + (491683639488627/25000000000000 : ℝ)*(major1) + (491683639488627/25000000000000 : ℝ)*(major2) + (258006143/50000000000000 : ℝ)*(sp2) + (1436362368994507/50000000000000 : ℝ)*(sp4) + (2872724054796737/100000000000000 : ℝ)*(sp5) + (718180878568153/25000000000000 : ℝ)*(sp6) + (530372113278489/50000000000000 : ℝ)*(sp7) + (530372113278489/50000000000000 : ℝ)*(f.failure) + (1436362368994507/50000000000000 : ℝ)*(f.sum) + (234403475887/99218750000000000000000000 : ℝ)*base65 + (242147887137241439/15875000000000000000000000000000 : ℝ)*base68 + (142714368929491439/15875000000000000000000000000000 : ℝ)*base70 + (1203458067272116439/15875000000000000000000000000000 : ℝ)*base72 + (7117686451909/3175000000000000000000000000 : ℝ)*base73 + (392944006014633561/15875000000000000000000000000000 : ℝ)*base75 + (32591073999991439/15875000000000000000000000000000 : ℝ)*base78 + (17784472294991439/15875000000000000000000000000000 : ℝ)*base80 + (378782877279/793750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (20572491/5000000000000000000000 : ℝ)*base89 + (20572491/5000000000000000000000 : ℝ)*base91 + (20572491/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1681_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (185410819/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1733/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (971/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1217/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17299/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1681_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1681_s4_0 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-304837719/2000000000 : ℝ)*x 0 + (5489332537/10000000000 : ℝ)*x 1 + (1283407887/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (304837719/2000000000 : ℝ)^5071 ≤ (9469466173113/100000000000000 : ℝ)^4047 := by
    have hnat : (304837719 : ℕ)^5071*100000000000000^4047 ≤ 9469466173113^4047*2000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      304837719 2000000000 9469466173113 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5489332537/10000000000 : ℝ)^5071 ≤ (1886561468357/4000000000000 : ℝ)^4047 := by
    have hnat : (5489332537 : ℕ)^5071*4000000000000^4047 ≤ 1886561468357^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5489332537 10000000000 1886561468357 4000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1283407887/2500000000 : ℝ)^5071 ≤ (43366497106549/100000000000000 : ℝ)^4047 := by
    have hnat : (1283407887 : ℕ)^5071*100000000000000^4047 ≤ 43366497106549^4047*2500000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1283407887 2500000000 43366497106549 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-304837719/2000000000 : ℝ), (5489332537/10000000000 : ℝ), (1283407887/2500000000 : ℝ)] ![(9469466173113/100000000000000 : ℝ), (1886561468357/4000000000000 : ℝ), (43366497106549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-304837719/2000000000 : ℝ)|^5071 ≤ (9469466173113/100000000000000 : ℝ)^4047
        have hw : |(-304837719/2000000000 : ℝ)|=(304837719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5489332537/10000000000 : ℝ)|^5071 ≤ (1886561468357/4000000000000 : ℝ)^4047
        have hw : |(5489332537/10000000000 : ℝ)|=(5489332537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1283407887/2500000000 : ℝ)|^5071 ≤ (43366497106549/100000000000000 : ℝ)^4047
        have hw : |(1283407887/2500000000 : ℝ)|=(1283407887/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_s4_1 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338298237/2500000000 : ℝ)*x 0 + (-854555761/5000000000 : ℝ)*x 1 + (5133630919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338298237/2500000000 : ℝ)^5071 ≤ (9140598781957/20000000000000 : ℝ)^4047 := by
    have hnat : (1338298237 : ℕ)^5071*20000000000000^4047 ≤ 9140598781957^4047*2500000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338298237 2500000000 9140598781957 20000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (854555761/5000000000 : ℝ)^5071 ≤ (2732628906827/25000000000000 : ℝ)^4047 := by
    have hnat : (854555761 : ℕ)^5071*25000000000000^4047 ≤ 2732628906827^4047*5000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854555761 5000000000 2732628906827 25000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5133630919/10000000000 : ℝ)^5071 ≤ (43366490448597/100000000000000 : ℝ)^4047 := by
    have hnat : (5133630919 : ℕ)^5071*100000000000000^4047 ≤ 43366490448597^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5133630919 10000000000 43366490448597 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338298237/2500000000 : ℝ), (-854555761/5000000000 : ℝ), (5133630919/10000000000 : ℝ)] ![(9140598781957/20000000000000 : ℝ), (2732628906827/25000000000000 : ℝ), (43366490448597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338298237/2500000000 : ℝ)|^5071 ≤ (9140598781957/20000000000000 : ℝ)^4047
        have hw : |(1338298237/2500000000 : ℝ)|=(1338298237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-854555761/5000000000 : ℝ)|^5071 ≤ (2732628906827/25000000000000 : ℝ)^4047
        have hw : |(-854555761/5000000000 : ℝ)|=(854555761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5133630919/10000000000 : ℝ)|^5071 ≤ (43366490448597/100000000000000 : ℝ)^4047
        have hw : |(5133630919/10000000000 : ℝ)|=(5133630919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_s4_2 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353192313/10000000000 : ℝ)*x 0 + (5133631337/10000000000 : ℝ)*x 1 + (-1709111817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353192313/10000000000 : ℝ)^5071 ≤ (22851493558359/50000000000000 : ℝ)^4047 := by
    have hnat : (5353192313 : ℕ)^5071*50000000000000^4047 ≤ 22851493558359^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353192313 10000000000 22851493558359 50000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5133631337/10000000000 : ℝ)^5071 ≤ (21683247436559/50000000000000 : ℝ)^4047 := by
    have hnat : (5133631337 : ℕ)^5071*50000000000000^4047 ≤ 21683247436559^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5133631337 10000000000 21683247436559 50000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1709111817/10000000000 : ℝ)^5071 ≤ (1366314748917/12500000000000 : ℝ)^4047 := by
    have hnat : (1709111817 : ℕ)^5071*12500000000000^4047 ≤ 1366314748917^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1709111817 10000000000 1366314748917 12500000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353192313/10000000000 : ℝ), (5133631337/10000000000 : ℝ), (-1709111817/10000000000 : ℝ)] ![(22851493558359/50000000000000 : ℝ), (21683247436559/50000000000000 : ℝ), (1366314748917/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353192313/10000000000 : ℝ)|^5071 ≤ (22851493558359/50000000000000 : ℝ)^4047
        have hw : |(5353192313/10000000000 : ℝ)|=(5353192313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5133631337/10000000000 : ℝ)|^5071 ≤ (21683247436559/50000000000000 : ℝ)^4047
        have hw : |(5133631337/10000000000 : ℝ)|=(5133631337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1709111817/10000000000 : ℝ)|^5071 ≤ (1366314748917/12500000000000 : ℝ)^4047
        have hw : |(-1709111817/10000000000 : ℝ)|=(1709111817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_s4_3 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4143782181/10000000000 : ℝ)*x 0 + (3681278167/10000000000 : ℝ)*x 1 + (4644593319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4143782181/10000000000 : ℝ)^5071 ≤ (33157977618977/100000000000000 : ℝ)^4047 := by
    have hnat : (4143782181 : ℕ)^5071*100000000000000^4047 ≤ 33157977618977^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4143782181 10000000000 33157977618977 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3681278167/10000000000 : ℝ)^5071 ≤ (7147013612529/25000000000000 : ℝ)^4047 := by
    have hnat : (3681278167 : ℕ)^5071*25000000000000^4047 ≤ 7147013612529^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3681278167 10000000000 7147013612529 25000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4644593319/10000000000 : ℝ)^5071 ≤ (19126983955117/50000000000000 : ℝ)^4047 := by
    have hnat : (4644593319 : ℕ)^5071*50000000000000^4047 ≤ 19126983955117^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4644593319 10000000000 19126983955117 50000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4143782181/10000000000 : ℝ), (3681278167/10000000000 : ℝ), (4644593319/10000000000 : ℝ)] ![(33157977618977/100000000000000 : ℝ), (7147013612529/25000000000000 : ℝ), (19126983955117/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4143782181/10000000000 : ℝ)|^5071 ≤ (33157977618977/100000000000000 : ℝ)^4047
        have hw : |(4143782181/10000000000 : ℝ)|=(4143782181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3681278167/10000000000 : ℝ)|^5071 ≤ (7147013612529/25000000000000 : ℝ)^4047
        have hw : |(3681278167/10000000000 : ℝ)|=(3681278167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4644593319/10000000000 : ℝ)|^5071 ≤ (19126983955117/50000000000000 : ℝ)^4047
        have hw : |(4644593319/10000000000 : ℝ)|=(4644593319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_s4_4 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1524355987/10000000000 : ℝ)*x 0 + (5137471147/10000000000 : ℝ)*x 1 + (2742717863/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1524355987/10000000000 : ℝ)^5071 ≤ (2367692325917/25000000000000 : ℝ)^4047 := by
    have hnat : (1524355987 : ℕ)^5071*25000000000000^4047 ≤ 2367692325917^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1524355987 10000000000 2367692325917 25000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5137471147/10000000000 : ℝ)^5071 ≤ (21703571515679/50000000000000 : ℝ)^4047 := by
    have hnat : (5137471147 : ℕ)^5071*50000000000000^4047 ≤ 21703571515679^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137471147 10000000000 21703571515679 50000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2742717863/5000000000 : ℝ)^5071 ≤ (9424417531129/20000000000000 : ℝ)^4047 := by
    have hnat : (2742717863 : ℕ)^5071*20000000000000^4047 ≤ 9424417531129^4047*5000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2742717863 5000000000 9424417531129 20000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1524355987/10000000000 : ℝ), (5137471147/10000000000 : ℝ), (2742717863/5000000000 : ℝ)] ![(2367692325917/25000000000000 : ℝ), (21703571515679/50000000000000 : ℝ), (9424417531129/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1524355987/10000000000 : ℝ)|^5071 ≤ (2367692325917/25000000000000 : ℝ)^4047
        have hw : |(-1524355987/10000000000 : ℝ)|=(1524355987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5137471147/10000000000 : ℝ)|^5071 ≤ (21703571515679/50000000000000 : ℝ)^4047
        have hw : |(5137471147/10000000000 : ℝ)|=(5137471147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2742717863/5000000000 : ℝ)|^5071 ≤ (9424417531129/20000000000000 : ℝ)^4047
        have hw : |(2742717863/5000000000 : ℝ)|=(2742717863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_s4_5 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5258199641/10000000000 : ℝ)*x 0 + (-339326833/2500000000 : ℝ)*x 1 + (5485435747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5258199641/10000000000 : ℝ)^5071 ≤ (22344535744129/50000000000000 : ℝ)^4047 := by
    have hnat : (5258199641 : ℕ)^5071*50000000000000^4047 ≤ 22344535744129^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258199641 10000000000 22344535744129 50000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339326833/2500000000 : ℝ)^5071 ≤ (8188840618751/100000000000000 : ℝ)^4047 := by
    have hnat : (339326833 : ℕ)^5071*100000000000000^4047 ≤ 8188840618751^4047*2500000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339326833 2500000000 8188840618751 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5485435747/10000000000 : ℝ)^5071 ≤ (47122087881689/100000000000000 : ℝ)^4047 := by
    have hnat : (5485435747 : ℕ)^5071*100000000000000^4047 ≤ 47122087881689^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5485435747 10000000000 47122087881689 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5258199641/10000000000 : ℝ), (-339326833/2500000000 : ℝ), (5485435747/10000000000 : ℝ)] ![(22344535744129/50000000000000 : ℝ), (8188840618751/100000000000000 : ℝ), (47122087881689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5258199641/10000000000 : ℝ)|^5071 ≤ (22344535744129/50000000000000 : ℝ)^4047
        have hw : |(5258199641/10000000000 : ℝ)|=(5258199641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-339326833/2500000000 : ℝ)|^5071 ≤ (8188840618751/100000000000000 : ℝ)^4047
        have hw : |(-339326833/2500000000 : ℝ)|=(339326833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5485435747/10000000000 : ℝ)|^5071 ≤ (47122087881689/100000000000000 : ℝ)^4047
        have hw : |(5485435747/10000000000 : ℝ)|=(5485435747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_s4_6 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314549931/2500000000 : ℝ)*x 0 + (2742717853/5000000000 : ℝ)*x 1 + (-169663409/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314549931/2500000000 : ℝ)^5071 ≤ (44689072372157/100000000000000 : ℝ)^4047 := by
    have hnat : (1314549931 : ℕ)^5071*100000000000000^4047 ≤ 44689072372157^4047*2500000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314549931 2500000000 44689072372157 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2742717853/5000000000 : ℝ)^5071 ≤ (9424417488073/20000000000000 : ℝ)^4047 := by
    have hnat : (2742717853 : ℕ)^5071*20000000000000^4047 ≤ 9424417488073^4047*5000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2742717853 5000000000 9424417488073 20000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169663409/1250000000 : ℝ)^5071 ≤ (8188840165169/100000000000000 : ℝ)^4047 := by
    have hnat : (169663409 : ℕ)^5071*100000000000000^4047 ≤ 8188840165169^4047*1250000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169663409 1250000000 8188840165169 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314549931/2500000000 : ℝ), (2742717853/5000000000 : ℝ), (-169663409/1250000000 : ℝ)] ![(44689072372157/100000000000000 : ℝ), (9424417488073/20000000000000 : ℝ), (8188840165169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314549931/2500000000 : ℝ)|^5071 ≤ (44689072372157/100000000000000 : ℝ)^4047
        have hw : |(1314549931/2500000000 : ℝ)|=(1314549931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2742717853/5000000000 : ℝ)|^5071 ≤ (9424417488073/20000000000000 : ℝ)^4047
        have hw : |(2742717853/5000000000 : ℝ)|=(2742717853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-169663409/1250000000 : ℝ)|^5071 ≤ (8188840165169/100000000000000 : ℝ)^4047
        have hw : |(-169663409/1250000000 : ℝ)|=(169663409/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_s4_7 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2072117921/5000000000 : ℝ)*x 0 + (4634195173/10000000000 : ℝ)*x 1 + (3691831809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2072117921/5000000000 : ℝ)^5071 ≤ (16581263168327/50000000000000 : ℝ)^4047 := by
    have hnat : (2072117921 : ℕ)^5071*50000000000000^4047 ≤ 16581263168327^4047*5000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072117921 5000000000 16581263168327 50000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4634195173/10000000000 : ℝ)^5071 ≤ (7629337421209/20000000000000 : ℝ)^4047 := by
    have hnat : (4634195173 : ℕ)^5071*20000000000000^4047 ≤ 7629337421209^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4634195173 10000000000 7629337421209 20000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3691831809/10000000000 : ℝ)^5071 ≤ (2869078653569/10000000000000 : ℝ)^4047 := by
    have hnat : (3691831809 : ℕ)^5071*10000000000000^4047 ≤ 2869078653569^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3691831809 10000000000 2869078653569 10000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2072117921/5000000000 : ℝ), (4634195173/10000000000 : ℝ), (3691831809/10000000000 : ℝ)] ![(16581263168327/50000000000000 : ℝ), (7629337421209/20000000000000 : ℝ), (2869078653569/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2072117921/5000000000 : ℝ)|^5071 ≤ (16581263168327/50000000000000 : ℝ)^4047
        have hw : |(2072117921/5000000000 : ℝ)|=(2072117921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4634195173/10000000000 : ℝ)|^5071 ≤ (7629337421209/20000000000000 : ℝ)^4047
        have hw : |(4634195173/10000000000 : ℝ)|=(4634195173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3691831809/10000000000 : ℝ)|^5071 ≤ (2869078653569/10000000000000 : ℝ)^4047
        have hw : |(3691831809/10000000000 : ℝ)|=(3691831809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1681_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (185410819/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17299/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1217/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (9737/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8649/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17299/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1217/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17299/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1217/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17299/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1217/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17299/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1217/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17299/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1217/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17299/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1217/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1217/12500 : ℝ) ^ (5063/1024 : ℝ) ≤ (497947639422911/50000000000000000000 : ℝ) := by
    have hpowers : (1217/12500 : ℝ)^5063 ≤ (497947639422911/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1217 : ℕ)^5063*50000000000000000000^1024 ≤ 497947639422911^1024*12500^5063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1217 12500 497947639422911 50000000000000000000 5063 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1217/12500 : ℝ)) (X := (497947639422911/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5063 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17299/100000 : ℝ) ^ (5063/1024 : ℝ) ≤ (8540628758010033/50000000000000000000 : ℝ) := by
    have hpowers : (17299/100000 : ℝ)^5063 ≤ (8540628758010033/50000000000000000000 : ℝ)^1024 := by
      have hnat : (17299 : ℕ)^5063*50000000000000000000^1024 ≤ 8540628758010033^1024*100000^5063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17299 100000 8540628758010033 50000000000000000000 5063 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17299/100000 : ℝ)) (X := (8540628758010033/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5063 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000497947639422911/25000000000000000000 : ℝ) ≤ (5000020141984271/5000000000000000 : ℝ) ^ (5063/1024 : ℝ) := by
    have hpowers : (25000497947639422911/25000000000000000000 : ℝ)^1024 ≤ (5000020141984271/5000000000000000 : ℝ)^5063 := by
      have hnat : (25000497947639422911 : ℕ)^1024*5000000000000000^5063 ≤ 5000020141984271^5063*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000497947639422911 25000000000000000000 5000020141984271 5000000000000000 1024 5063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000020141984271/5000000000000000 : ℝ)) (X := (25000497947639422911/25000000000000000000 : ℝ)) (by norm_num) 5063 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3125564911024839559/3125000000000000000 : ℝ) ≤ (10000365587001161/10000000000000000 : ℝ) ^ (5063/1024 : ℝ) := by
    have hpowers : (3125564911024839559/3125000000000000000 : ℝ)^1024 ≤ (10000365587001161/10000000000000000 : ℝ)^5063 := by
      have hnat : (3125564911024839559 : ℕ)^1024*10000000000000000^5063 ≤ 10000365587001161^5063*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125564911024839559 3125000000000000000 10000365587001161 10000000000000000 1024 5063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000365587001161/10000000000000000 : ℝ)) (X := (3125564911024839559/3125000000000000000 : ℝ)) (by norm_num) 5063 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25008540628758010033/25000000000000000000 : ℝ) ≤ (500034544501689/500000000000000 : ℝ) ^ (5063/1024 : ℝ) := by
    have hpowers : (25008540628758010033/25000000000000000000 : ℝ)^1024 ≤ (500034544501689/500000000000000 : ℝ)^5063 := by
      have hnat : (25008540628758010033 : ℕ)^1024*500000000000000^5063 ≤ 500034544501689^5063*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008540628758010033 25000000000000000000 500034544501689 500000000000000 1024 5063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500034544501689/500000000000000 : ℝ)) (X := (25008540628758010033/25000000000000000000 : ℝ)) (by norm_num) 5063 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(497947639422911/50000000000000000000 : ℝ) ≤ ((37811985183501462989/37815000000000000000 : ℝ)+2*(325303032619/756300000000000 : ℝ)*(1217/12500 : ℝ))^(5063/1024 : ℝ) := by
    rw [show (37811985183501462989/37815000000000000000 : ℝ)+2*(325303032619/756300000000000 : ℝ)*(1217/12500 : ℝ)=(5000020141984271/5000000000000000 : ℝ) by norm_num, show 1+2*(497947639422911/50000000000000000000 : ℝ)=(25000497947639422911/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8540628758010033/50000000000000000000 : ℝ)+(497947639422911/50000000000000000000 : ℝ) ≤ ((37811985183501462989/37815000000000000000 : ℝ)+(325303032619/756300000000000 : ℝ)*((17299/100000 : ℝ)+(1217/12500 : ℝ)))^(5063/1024 : ℝ) := by
    rw [show (37811985183501462989/37815000000000000000 : ℝ)+(325303032619/756300000000000 : ℝ)*((17299/100000 : ℝ)+(1217/12500 : ℝ))=(10000365587001161/10000000000000000 : ℝ) by norm_num, show 1+(8540628758010033/50000000000000000000 : ℝ)+(497947639422911/50000000000000000000 : ℝ)=(3125564911024839559/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8540628758010033/50000000000000000000 : ℝ) ≤ ((37811985183501462989/37815000000000000000 : ℝ)+2*(325303032619/756300000000000 : ℝ)*(17299/100000 : ℝ))^(5063/1024 : ℝ) := by
    rw [show (37811985183501462989/37815000000000000000 : ℝ)+2*(325303032619/756300000000000 : ℝ)*(17299/100000 : ℝ)=(500034544501689/500000000000000 : ℝ) by norm_num, show 1+2*(8540628758010033/50000000000000000000 : ℝ)=(25008540628758010033/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37811985183501462989/37815000000000000000 : ℝ)*(X 1 0+X 2 0)+(325303032619/756300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5063/1024 : ℝ)) (lo := (1217/12500 : ℝ)) (hi := (17299/100000 : ℝ)) (c := (37811985183501462989/37815000000000000000 : ℝ)) (alpha := (325303032619/756300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37811985183501462989/37815000000000000000 : ℝ)*(X 0 1+X 2 1)+(325303032619/756300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5063/1024 : ℝ)) (lo := (1217/12500 : ℝ)) (hi := (17299/100000 : ℝ)) (c := (37811985183501462989/37815000000000000000 : ℝ)) (alpha := (325303032619/756300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37811985183501462989/37815000000000000000 : ℝ)*(X 0 2+X 1 2)+(325303032619/756300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5063/1024 : ℝ)) (lo := (1217/12500 : ℝ)) (hi := (17299/100000 : ℝ)) (c := (37811985183501462989/37815000000000000000 : ℝ)) (alpha := (325303032619/756300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-304837719/2000000000 : ℝ)*X 0 0+(5489332537/10000000000 : ℝ)*X 0 1+(1283407887/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338298237/2500000000 : ℝ)*X 1 0+(-854555761/5000000000 : ℝ)*X 1 1+(5133630919/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353192313/10000000000 : ℝ)*X 2 0+(5133631337/10000000000 : ℝ)*X 2 1+(-1709111817/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4143782181/10000000000 : ℝ)*X 0 0+(3681278167/10000000000 : ℝ)*X 0 1+(4644593319/10000000000 : ℝ)*X 0 2+(4143782181/10000000000 : ℝ)*X 1 0+(3681278167/10000000000 : ℝ)*X 1 1+(4644593319/10000000000 : ℝ)*X 1 2+(4143782181/10000000000 : ℝ)*X 2 0+(3681278167/10000000000 : ℝ)*X 2 1+(4644593319/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1524355987/10000000000 : ℝ)*X 0 0+(5137471147/10000000000 : ℝ)*X 0 1+(2742717863/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5258199641/10000000000 : ℝ)*X 1 0+(-339326833/2500000000 : ℝ)*X 1 1+(5485435747/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1314549931/2500000000 : ℝ)*X 2 0+(2742717853/5000000000 : ℝ)*X 2 1+(-169663409/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2072117921/5000000000 : ℝ)*X 0 0+(4634195173/10000000000 : ℝ)*X 0 1+(3691831809/10000000000 : ℝ)*X 0 2+(2072117921/5000000000 : ℝ)*X 1 0+(4634195173/10000000000 : ℝ)*X 1 1+(3691831809/10000000000 : ℝ)*X 1 2+(2072117921/5000000000 : ℝ)*X 2 0+(4634195173/10000000000 : ℝ)*X 2 1+(3691831809/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (57259470514989945232767/6302500000000000000000000000 : ℝ) := by norm_num
    linear_combination (375383321/20000000000000 : ℝ)*(base19) + (377801119/25000000000000 : ℝ)*(base23) + (4312603/25000000000000 : ℝ)*(lower2) + (349882853/100000000000000 : ℝ)*(upper3) + (102952487/100000000000000 : ℝ)*(upper5) + (962367302151993/50000000000000 : ℝ)*(major0) + (962367302151993/50000000000000 : ℝ)*(major1) + (962367302151993/50000000000000 : ℝ)*(major2) + (281136606328829/10000000000000 : ℝ)*(sp0) + (175710948568767/6250000000000 : ℝ)*(sp1) + (2811375542812401/100000000000000 : ℝ)*(sp2) + (1038086276380157/100000000000000 : ℝ)*(sp3) + (5495364293/50000000000000 : ℝ)*(sp4) + (2787685473/50000000000000 : ℝ)*(sp7) + (1038091851751103/100000000000000 : ℝ)*(f.failure) + (702844263504219/25000000000000 : ℝ)*(f.sum) + (79138025334507/12605000000000000000000000000 : ℝ)*base66 + (7627604898034562359/630250000000000000000000000000000 : ℝ)*base67 + (2752209592263562359/630250000000000000000000000000000 : ℝ)*base69 + (1241925446009437641/630250000000000000000000000000000 : ℝ)*base72 + (62942889178513/12605000000000000000000000000 : ℝ)*base73 + (1360596201699437641/630250000000000000000000000000000 : ℝ)*base76 + (1415238937833687641/630250000000000000000000000000000 : ℝ)*base78 + (1139426778518312359/630250000000000000000000000000000 : ℝ)*base79 + (7548012868561/6302500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (8616643/10000000000000000000000 : ℝ)*base90 + (8616643/10000000000000000000000 : ℝ)*base92 + (8616643/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1883014889762744544540995301/157562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1674926949/100000000000000 : ℝ)*(base19) + (1876872407/100000000000000 : ℝ)*(base23) + (509258357/100000000000000 : ℝ)*(lower1) + (50586649/20000000000000 : ℝ)*(upper3) + (65829581/100000000000000 : ℝ)*(lower4) + (123674747/50000000000000 : ℝ)*(upper5) + (983749271653109/50000000000000 : ℝ)*(major0) + (983749271653109/50000000000000 : ℝ)*(major1) + (983749271653109/50000000000000 : ℝ)*(major2) + (1737452663/100000000000000 : ℝ)*(sp2) + (359230051456627/12500000000000 : ℝ)*(sp4) + (2873838736726067/100000000000000 : ℝ)*(sp5) + (574767359465589/20000000000000 : ℝ)*(sp6) + (530578138297911/50000000000000 : ℝ)*(sp7) + (530578138297911/50000000000000 : ℝ)*(f.failure) + (359230051456627/12500000000000 : ℝ)*(f.sum) + (73973880647681/18907500000000000000000000000 : ℝ)*base65 + (21858682615904667199/1890750000000000000000000000000000 : ℝ)*base68 + (14361395738036667199/1890750000000000000000000000000000 : ℝ)*base70 + (10013885463609417199/1890750000000000000000000000000000 : ℝ)*base72 + (13785036450239/4726875000000000000000000000 : ℝ)*base73 + (63184940963018582801/1890750000000000000000000000000000 : ℝ)*base75 + (739236288453417199/1890750000000000000000000000000000 : ℝ)*base78 + (2856598317951417199/1890750000000000000000000000000000 : ℝ)*base80 + (169460834432963/37815000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (44499109/5000000000000000000000 : ℝ)*base89 + (44499109/5000000000000000000000 : ℝ)*base91 + (44499109/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1681_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (185410819/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17299/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1217/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9737/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8649/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1681_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1681_box_0 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-590642523/5000000000 : ℝ)*x 0 + (5433120533/10000000000 : ℝ)*x 1 + (1086623349/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (590642523/5000000000 : ℝ)^5071 ≤ (1376148996569/20000000000000 : ℝ)^4047 := by
    have hnat : (590642523 : ℕ)^5071*20000000000000^4047 ≤ 1376148996569^4047*5000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      590642523 5000000000 1376148996569 20000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433120533/10000000000 : ℝ)^5071 ≤ (4655964784307/10000000000000 : ℝ)^4047 := by
    have hnat : (5433120533 : ℕ)^5071*10000000000000^4047 ≤ 4655964784307^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433120533 10000000000 4655964784307 10000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086623349/2000000000 : ℝ)^5071 ≤ (23279803583889/50000000000000 : ℝ)^4047 := by
    have hnat : (1086623349 : ℕ)^5071*50000000000000^4047 ≤ 23279803583889^4047*2000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086623349 2000000000 23279803583889 50000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-590642523/5000000000 : ℝ), (5433120533/10000000000 : ℝ), (1086623349/2000000000 : ℝ)] ![(1376148996569/20000000000000 : ℝ), (4655964784307/10000000000000 : ℝ), (23279803583889/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-590642523/5000000000 : ℝ)|^5071 ≤ (1376148996569/20000000000000 : ℝ)^4047
        have hw : |(-590642523/5000000000 : ℝ)|=(590642523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433120533/10000000000 : ℝ)|^5071 ≤ (4655964784307/10000000000000 : ℝ)^4047
        have hw : |(5433120533/10000000000 : ℝ)|=(5433120533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1086623349/2000000000 : ℝ)|^5071 ≤ (23279803583889/50000000000000 : ℝ)^4047
        have hw : |(1086623349/2000000000 : ℝ)|=(1086623349/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_box_1 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (653261327/1250000000 : ℝ)*x 0 + (-295125853/2000000000 : ℝ)*x 1 + (5433118661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (653261327/1250000000 : ℝ)^5071 ≤ (2771712161247/6250000000000 : ℝ)^4047 := by
    have hnat : (653261327 : ℕ)^5071*6250000000000^4047 ≤ 2771712161247^4047*1250000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653261327 1250000000 2771712161247 6250000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (295125853/2000000000 : ℝ)^5071 ≤ (9092977657581/100000000000000 : ℝ)^4047 := by
    have hnat : (295125853 : ℕ)^5071*100000000000000^4047 ≤ 9092977657581^4047*2000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      295125853 2000000000 9092977657581 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5433118661/10000000000 : ℝ)^5071 ≤ (46559627741657/100000000000000 : ℝ)^4047 := by
    have hnat : (5433118661 : ℕ)^5071*100000000000000^4047 ≤ 46559627741657^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433118661 10000000000 46559627741657 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(653261327/1250000000 : ℝ), (-295125853/2000000000 : ℝ), (5433118661/10000000000 : ℝ)] ![(2771712161247/6250000000000 : ℝ), (9092977657581/100000000000000 : ℝ), (46559627741657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(653261327/1250000000 : ℝ)|^5071 ≤ (2771712161247/6250000000000 : ℝ)^4047
        have hw : |(653261327/1250000000 : ℝ)|=(653261327/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-295125853/2000000000 : ℝ)|^5071 ≤ (9092977657581/100000000000000 : ℝ)^4047
        have hw : |(-295125853/2000000000 : ℝ)|=(295125853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5433118661/10000000000 : ℝ)|^5071 ≤ (46559627741657/100000000000000 : ℝ)^4047
        have hw : |(5433118661/10000000000 : ℝ)|=(5433118661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_box_2 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2613045969/5000000000 : ℝ)*x 0 + (27165583/50000000 : ℝ)*x 1 + (-1475630311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2613045969/5000000000 : ℝ)^5071 ≤ (44347408636641/100000000000000 : ℝ)^4047 := by
    have hnat : (2613045969 : ℕ)^5071*100000000000000^4047 ≤ 44347408636641^4047*5000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613045969 5000000000 44347408636641 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27165583/50000000 : ℝ)^5071 ≤ (46559605610777/100000000000000 : ℝ)^4047 := by
    have hnat : (27165583 : ℕ)^5071*100000000000000^4047 ≤ 46559605610777^4047*50000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27165583 50000000 46559605610777 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1475630311/10000000000 : ℝ)^5071 ≤ (227324643351/2500000000000 : ℝ)^4047 := by
    have hnat : (1475630311 : ℕ)^5071*2500000000000^4047 ≤ 227324643351^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1475630311 10000000000 227324643351 2500000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2613045969/5000000000 : ℝ), (27165583/50000000 : ℝ), (-1475630311/10000000000 : ℝ)] ![(44347408636641/100000000000000 : ℝ), (46559605610777/100000000000000 : ℝ), (227324643351/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2613045969/5000000000 : ℝ)|^5071 ≤ (44347408636641/100000000000000 : ℝ)^4047
        have hw : |(2613045969/5000000000 : ℝ)|=(2613045969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(27165583/50000000 : ℝ)|^5071 ≤ (46559605610777/100000000000000 : ℝ)^4047
        have hw : |(27165583/50000000 : ℝ)|=(27165583/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1475630311/10000000000 : ℝ)|^5071 ≤ (227324643351/2500000000000 : ℝ)^4047
        have hw : |(-1475630311/10000000000 : ℝ)|=(1475630311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_box_3 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (283088311/625000000 : ℝ)*x 0 + (794818889/2000000000 : ℝ)*x 1 + (1987045441/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (283088311/625000000 : ℝ)^5071 ≤ (18534516700817/50000000000000 : ℝ)^4047 := by
    have hnat : (283088311 : ℕ)^5071*50000000000000^4047 ≤ 18534516700817^4047*625000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283088311 625000000 18534516700817 50000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (794818889/2000000000 : ℝ)^5071 ≤ (15732750482907/50000000000000 : ℝ)^4047 := by
    have hnat : (794818889 : ℕ)^5071*50000000000000^4047 ≤ 15732750482907^4047*2000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      794818889 2000000000 15732750482907 50000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1987045441/5000000000 : ℝ)^5071 ≤ (31465465617179/100000000000000 : ℝ)^4047 := by
    have hnat : (1987045441 : ℕ)^5071*100000000000000^4047 ≤ 31465465617179^4047*5000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1987045441 5000000000 31465465617179 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(283088311/625000000 : ℝ), (794818889/2000000000 : ℝ), (1987045441/5000000000 : ℝ)] ![(18534516700817/50000000000000 : ℝ), (15732750482907/50000000000000 : ℝ), (31465465617179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(283088311/625000000 : ℝ)|^5071 ≤ (18534516700817/50000000000000 : ℝ)^4047
        have hw : |(283088311/625000000 : ℝ)|=(283088311/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(794818889/2000000000 : ℝ)|^5071 ≤ (15732750482907/50000000000000 : ℝ)^4047
        have hw : |(794818889/2000000000 : ℝ)|=(794818889/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1987045441/5000000000 : ℝ)|^5071 ≤ (31465465617179/100000000000000 : ℝ)^4047
        have hw : |(1987045441/5000000000 : ℝ)|=(1987045441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_box_4 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1888192287/10000000000 : ℝ)*x 0 + (5175291999/10000000000 : ℝ)*x 1 + (5175291623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1888192287/10000000000 : ℝ)^5071 ≤ (387004875039/3125000000000 : ℝ)^4047 := by
    have hnat : (1888192287 : ℕ)^5071*3125000000000^4047 ≤ 387004875039^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1888192287 10000000000 387004875039 3125000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5175291999/10000000000 : ℝ)^5071 ≤ (21903961995003/50000000000000 : ℝ)^4047 := by
    have hnat : (5175291999 : ℕ)^5071*50000000000000^4047 ≤ 21903961995003^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175291999 10000000000 21903961995003 50000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5175291623/10000000000 : ℝ)^5071 ≤ (21903960000953/50000000000000 : ℝ)^4047 := by
    have hnat : (5175291623 : ℕ)^5071*50000000000000^4047 ≤ 21903960000953^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175291623 10000000000 21903960000953 50000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1888192287/10000000000 : ℝ), (5175291999/10000000000 : ℝ), (5175291623/10000000000 : ℝ)] ![(387004875039/3125000000000 : ℝ), (21903961995003/50000000000000 : ℝ), (21903960000953/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1888192287/10000000000 : ℝ)|^5071 ≤ (387004875039/3125000000000 : ℝ)^4047
        have hw : |(-1888192287/10000000000 : ℝ)|=(1888192287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5175291999/10000000000 : ℝ)|^5071 ≤ (21903961995003/50000000000000 : ℝ)^4047
        have hw : |(5175291999/10000000000 : ℝ)|=(5175291999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5175291623/10000000000 : ℝ)|^5071 ≤ (21903960000953/50000000000000 : ℝ)^4047
        have hw : |(5175291623/10000000000 : ℝ)|=(5175291623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_box_5 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (540220293/1000000000 : ℝ)*x 0 + (-793704659/5000000000 : ℝ)*x 1 + (1293822929/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540220293/1000000000 : ℝ)^5071 ≤ (46227895996727/100000000000000 : ℝ)^4047 := by
    have hnat : (540220293 : ℕ)^5071*100000000000000^4047 ≤ 46227895996727^4047*1000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540220293 1000000000 46227895996727 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (793704659/5000000000 : ℝ)^5071 ≤ (4982091499847/50000000000000 : ℝ)^4047 := by
    have hnat : (793704659 : ℕ)^5071*50000000000000^4047 ≤ 4982091499847^4047*5000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      793704659 5000000000 4982091499847 50000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1293822929/2500000000 : ℝ)^5071 ≤ (10951980247081/25000000000000 : ℝ)^4047 := by
    have hnat : (1293822929 : ℕ)^5071*25000000000000^4047 ≤ 10951980247081^4047*2500000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293822929 2500000000 10951980247081 25000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540220293/1000000000 : ℝ), (-793704659/5000000000 : ℝ), (1293822929/2500000000 : ℝ)] ![(46227895996727/100000000000000 : ℝ), (4982091499847/50000000000000 : ℝ), (10951980247081/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540220293/1000000000 : ℝ)|^5071 ≤ (46227895996727/100000000000000 : ℝ)^4047
        have hw : |(540220293/1000000000 : ℝ)|=(540220293/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-793704659/5000000000 : ℝ)|^5071 ≤ (4982091499847/50000000000000 : ℝ)^4047
        have hw : |(-793704659/5000000000 : ℝ)|=(793704659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1293822929/2500000000 : ℝ)|^5071 ≤ (10951980247081/25000000000000 : ℝ)^4047
        have hw : |(1293822929/2500000000 : ℝ)|=(1293822929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_box_6 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5402202729/10000000000 : ℝ)*x 0 + (2587645929/5000000000 : ℝ)*x 1 + (-1587409401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5402202729/10000000000 : ℝ)^5071 ≤ (11556973460379/25000000000000 : ℝ)^4047 := by
    have hnat : (5402202729 : ℕ)^5071*25000000000000^4047 ≤ 11556973460379^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402202729 10000000000 11556973460379 25000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2587645929/5000000000 : ℝ)^5071 ≤ (10951980623617/25000000000000 : ℝ)^4047 := by
    have hnat : (2587645929 : ℕ)^5071*25000000000000^4047 ≤ 10951980623617^4047*5000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587645929 5000000000 10951980623617 25000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1587409401/10000000000 : ℝ)^5071 ≤ (9964183652511/100000000000000 : ℝ)^4047 := by
    have hnat : (1587409401 : ℕ)^5071*100000000000000^4047 ≤ 9964183652511^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1587409401 10000000000 9964183652511 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5402202729/10000000000 : ℝ), (2587645929/5000000000 : ℝ), (-1587409401/10000000000 : ℝ)] ![(11556973460379/25000000000000 : ℝ), (10951980623617/25000000000000 : ℝ), (9964183652511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5402202729/10000000000 : ℝ)|^5071 ≤ (11556973460379/25000000000000 : ℝ)^4047
        have hw : |(5402202729/10000000000 : ℝ)|=(5402202729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2587645929/5000000000 : ℝ)|^5071 ≤ (10951980623617/25000000000000 : ℝ)^4047
        have hw : |(2587645929/5000000000 : ℝ)|=(2587645929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1587409401/10000000000 : ℝ)|^5071 ≤ (9964183652511/100000000000000 : ℝ)^4047
        have hw : |(-1587409401/10000000000 : ℝ)|=(1587409401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_box_7 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1872041309/5000000000 : ℝ)*x 0 + (2182939751/5000000000 : ℝ)*x 1 + (4365879141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1872041309/5000000000 : ℝ)^5071 ≤ (29200502442023/100000000000000 : ℝ)^4047 := by
    have hnat : (1872041309 : ℕ)^5071*100000000000000^4047 ≤ 29200502442023^4047*5000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1872041309 5000000000 29200502442023 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2182939751/5000000000 : ℝ)^5071 ≤ (1769987530283/5000000000000 : ℝ)^4047 := by
    have hnat : (2182939751 : ℕ)^5071*5000000000000^4047 ≤ 1769987530283^4047*5000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182939751 5000000000 1769987530283 5000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4365879141/10000000000 : ℝ)^5071 ≤ (35399746937941/100000000000000 : ℝ)^4047 := by
    have hnat : (4365879141 : ℕ)^5071*100000000000000^4047 ≤ 35399746937941^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365879141 10000000000 35399746937941 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1872041309/5000000000 : ℝ), (2182939751/5000000000 : ℝ), (4365879141/10000000000 : ℝ)] ![(29200502442023/100000000000000 : ℝ), (1769987530283/5000000000000 : ℝ), (35399746937941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1872041309/5000000000 : ℝ)|^5071 ≤ (29200502442023/100000000000000 : ℝ)^4047
        have hw : |(1872041309/5000000000 : ℝ)|=(1872041309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2182939751/5000000000 : ℝ)|^5071 ≤ (1769987530283/5000000000000 : ℝ)^4047
        have hw : |(2182939751/5000000000 : ℝ)|=(2182939751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4365879141/10000000000 : ℝ)|^5071 ≤ (35399746937941/100000000000000 : ℝ)^4047
        have hw : |(4365879141/10000000000 : ℝ)|=(4365879141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_box_8 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1736707683/10000000000 : ℝ)*x 0 + (4986597339/10000000000 : ℝ)*x 1 + (5477070823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1736707683/10000000000 : ℝ)^5071 ≤ (2230422337931/20000000000000 : ℝ)^4047 := by
    have hnat : (1736707683 : ℕ)^5071*20000000000000^4047 ≤ 2230422337931^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1736707683 10000000000 2230422337931 20000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4986597339/10000000000 : ℝ)^5071 ≤ (41815823105043/100000000000000 : ℝ)^4047 := by
    have hnat : (4986597339 : ℕ)^5071*100000000000000^4047 ≤ 41815823105043^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4986597339 10000000000 41815823105043 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5477070823/10000000000 : ℝ)^5071 ≤ (47032065194577/100000000000000 : ℝ)^4047 := by
    have hnat : (5477070823 : ℕ)^5071*100000000000000^4047 ≤ 47032065194577^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5477070823 10000000000 47032065194577 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1736707683/10000000000 : ℝ), (4986597339/10000000000 : ℝ), (5477070823/10000000000 : ℝ)] ![(2230422337931/20000000000000 : ℝ), (41815823105043/100000000000000 : ℝ), (47032065194577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1736707683/10000000000 : ℝ)|^5071 ≤ (2230422337931/20000000000000 : ℝ)^4047
        have hw : |(-1736707683/10000000000 : ℝ)|=(1736707683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4986597339/10000000000 : ℝ)|^5071 ≤ (41815823105043/100000000000000 : ℝ)^4047
        have hw : |(4986597339/10000000000 : ℝ)|=(4986597339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5477070823/10000000000 : ℝ)|^5071 ≤ (47032065194577/100000000000000 : ℝ)^4047
        have hw : |(5477070823/10000000000 : ℝ)|=(5477070823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_box_9 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (324754691/625000000 : ℝ)*x 0 + (-1455712173/10000000000 : ℝ)*x 1 + (4381657/8000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (324754691/625000000 : ℝ)^5071 ≤ (44028474475921/100000000000000 : ℝ)^4047 := by
    have hnat : (324754691 : ℕ)^5071*100000000000000^4047 ≤ 44028474475921^4047*625000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324754691 625000000 44028474475921 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1455712173/10000000000 : ℝ)^5071 ≤ (2234863928971/25000000000000 : ℝ)^4047 := by
    have hnat : (1455712173 : ℕ)^5071*25000000000000^4047 ≤ 2234863928971^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1455712173 10000000000 2234863928971 25000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4381657/8000000 : ℝ)^5071 ≤ (5879008723629/12500000000000 : ℝ)^4047 := by
    have hnat : (4381657 : ℕ)^5071*12500000000000^4047 ≤ 5879008723629^4047*8000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4381657 8000000 5879008723629 12500000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(324754691/625000000 : ℝ), (-1455712173/10000000000 : ℝ), (4381657/8000000 : ℝ)] ![(44028474475921/100000000000000 : ℝ), (2234863928971/25000000000000 : ℝ), (5879008723629/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(324754691/625000000 : ℝ)|^5071 ≤ (44028474475921/100000000000000 : ℝ)^4047
        have hw : |(324754691/625000000 : ℝ)|=(324754691/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1455712173/10000000000 : ℝ)|^5071 ≤ (2234863928971/25000000000000 : ℝ)^4047
        have hw : |(-1455712173/10000000000 : ℝ)|=(1455712173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4381657/8000000 : ℝ)|^5071 ≤ (5879008723629/12500000000000 : ℝ)^4047
        have hw : |(4381657/8000000 : ℝ)|=(4381657/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_box_10 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196075063/10000000000 : ℝ)*x 0 + (5477071793/10000000000 : ℝ)*x 1 + (-363927851/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196075063/10000000000 : ℝ)^5071 ≤ (44028474550243/100000000000000 : ℝ)^4047 := by
    have hnat : (5196075063 : ℕ)^5071*100000000000000^4047 ≤ 44028474550243^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196075063 10000000000 44028474550243 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5477071793/10000000000 : ℝ)^5071 ≤ (47032075631629/100000000000000 : ℝ)^4047 := by
    have hnat : (5477071793 : ℕ)^5071*100000000000000^4047 ≤ 47032075631629^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5477071793 10000000000 47032075631629 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (363927851/2500000000 : ℝ)^5071 ≤ (8939449798601/100000000000000 : ℝ)^4047 := by
    have hnat : (363927851 : ℕ)^5071*100000000000000^4047 ≤ 8939449798601^4047*2500000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      363927851 2500000000 8939449798601 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196075063/10000000000 : ℝ), (5477071793/10000000000 : ℝ), (-363927851/2500000000 : ℝ)] ![(44028474550243/100000000000000 : ℝ), (47032075631629/100000000000000 : ℝ), (8939449798601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196075063/10000000000 : ℝ)|^5071 ≤ (44028474550243/100000000000000 : ℝ)^4047
        have hw : |(5196075063/10000000000 : ℝ)|=(5196075063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5477071793/10000000000 : ℝ)|^5071 ≤ (47032075631629/100000000000000 : ℝ)^4047
        have hw : |(5477071793/10000000000 : ℝ)|=(5477071793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-363927851/2500000000 : ℝ)|^5071 ≤ (8939449798601/100000000000000 : ℝ)^4047
        have hw : |(-363927851/2500000000 : ℝ)|=(363927851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_box_11 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2329121507/5000000000 : ℝ)*x 0 + (1953564851/5000000000 : ℝ)*x 1 + (122097753/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2329121507/5000000000 : ℝ)^5071 ≤ (38394888182369/100000000000000 : ℝ)^4047 := by
    have hnat : (2329121507 : ℕ)^5071*100000000000000^4047 ≤ 38394888182369^4047*5000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2329121507 5000000000 38394888182369 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1953564851/5000000000 : ℝ)^5071 ≤ (30802563835589/100000000000000 : ℝ)^4047 := by
    have hnat : (1953564851 : ℕ)^5071*100000000000000^4047 ≤ 30802563835589^4047*5000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1953564851 5000000000 30802563835589 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (122097753/312500000 : ℝ)^5071 ≤ (3850318496347/12500000000000 : ℝ)^4047 := by
    have hnat : (122097753 : ℕ)^5071*12500000000000^4047 ≤ 3850318496347^4047*312500000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122097753 312500000 3850318496347 12500000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2329121507/5000000000 : ℝ), (1953564851/5000000000 : ℝ), (122097753/312500000 : ℝ)] ![(38394888182369/100000000000000 : ℝ), (30802563835589/100000000000000 : ℝ), (3850318496347/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2329121507/5000000000 : ℝ)|^5071 ≤ (38394888182369/100000000000000 : ℝ)^4047
        have hw : |(2329121507/5000000000 : ℝ)|=(2329121507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1953564851/5000000000 : ℝ)|^5071 ≤ (30802563835589/100000000000000 : ℝ)^4047
        have hw : |(1953564851/5000000000 : ℝ)|=(1953564851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(122097753/312500000 : ℝ)|^5071 ≤ (3850318496347/12500000000000 : ℝ)^4047
        have hw : |(122097753/312500000 : ℝ)|=(122097753/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_box_12 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-132829321/1000000000 : ℝ)*x 0 + (87691059/156250000 : ℝ)*x 1 + (2574963587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132829321/1000000000 : ℝ)^5071 ≤ (7970098887131/100000000000000 : ℝ)^4047 := by
    have hnat : (132829321 : ℕ)^5071*100000000000000^4047 ≤ 7970098887131^4047*1000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132829321 1000000000 7970098887131 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (87691059/156250000 : ℝ)^5071 ≤ (48490845900591/100000000000000 : ℝ)^4047 := by
    have hnat : (87691059 : ℕ)^5071*100000000000000^4047 ≤ 48490845900591^4047*156250000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87691059 156250000 48490845900591 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2574963587/5000000000 : ℝ)^5071 ≤ (1741562208087/4000000000000 : ℝ)^4047 := by
    have hnat : (2574963587 : ℕ)^5071*4000000000000^4047 ≤ 1741562208087^4047*5000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2574963587 5000000000 1741562208087 4000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-132829321/1000000000 : ℝ), (87691059/156250000 : ℝ), (2574963587/5000000000 : ℝ)] ![(7970098887131/100000000000000 : ℝ), (48490845900591/100000000000000 : ℝ), (1741562208087/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-132829321/1000000000 : ℝ)|^5071 ≤ (7970098887131/100000000000000 : ℝ)^4047
        have hw : |(-132829321/1000000000 : ℝ)|=(132829321/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(87691059/156250000 : ℝ)|^5071 ≤ (48490845900591/100000000000000 : ℝ)^4047
        have hw : |(87691059/156250000 : ℝ)|=(87691059/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2574963587/5000000000 : ℝ)|^5071 ≤ (1741562208087/4000000000000 : ℝ)^4047
        have hw : |(2574963587/5000000000 : ℝ)|=(2574963587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_box_13 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1354888517/2500000000 : ℝ)*x 0 + (-6391681/40000000 : ℝ)*x 1 + (5149927489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1354888517/2500000000 : ℝ)^5071 ≤ (2320700903887/5000000000000 : ℝ)^4047 := by
    have hnat : (1354888517 : ℕ)^5071*5000000000000^4047 ≤ 2320700903887^4047*2500000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354888517 2500000000 2320700903887 5000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6391681/40000000 : ℝ)^5071 ≤ (2511730842559/25000000000000 : ℝ)^4047 := by
    have hnat : (6391681 : ℕ)^5071*25000000000000^4047 ≤ 2511730842559^4047*40000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6391681 40000000 2511730842559 25000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5149927489/10000000000 : ℝ)^5071 ≤ (43539058539119/100000000000000 : ℝ)^4047 := by
    have hnat : (5149927489 : ℕ)^5071*100000000000000^4047 ≤ 43539058539119^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5149927489 10000000000 43539058539119 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1354888517/2500000000 : ℝ), (-6391681/40000000 : ℝ), (5149927489/10000000000 : ℝ)] ![(2320700903887/5000000000000 : ℝ), (2511730842559/25000000000000 : ℝ), (43539058539119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1354888517/2500000000 : ℝ)|^5071 ≤ (2320700903887/5000000000000 : ℝ)^4047
        have hw : |(1354888517/2500000000 : ℝ)|=(1354888517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6391681/40000000 : ℝ)|^5071 ≤ (2511730842559/25000000000000 : ℝ)^4047
        have hw : |(-6391681/40000000 : ℝ)|=(6391681/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5149927489/10000000000 : ℝ)|^5071 ≤ (43539058539119/100000000000000 : ℝ)^4047
        have hw : |(5149927489/10000000000 : ℝ)|=(5149927489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_box_14 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5419553917/10000000000 : ℝ)*x 0 + (5149927291/10000000000 : ℝ)*x 1 + (-1597920723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5419553917/10000000000 : ℝ)^5071 ≤ (46414016457337/100000000000000 : ℝ)^4047 := by
    have hnat : (5419553917 : ℕ)^5071*100000000000000^4047 ≤ 46414016457337^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419553917 10000000000 46414016457337 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5149927291/10000000000 : ℝ)^5071 ≤ (43539056441611/100000000000000 : ℝ)^4047 := by
    have hnat : (5149927291 : ℕ)^5071*100000000000000^4047 ≤ 43539056441611^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5149927291 10000000000 43539056441611 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1597920723/10000000000 : ℝ)^5071 ≤ (10046927096723/100000000000000 : ℝ)^4047 := by
    have hnat : (1597920723 : ℕ)^5071*100000000000000^4047 ≤ 10046927096723^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1597920723 10000000000 10046927096723 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5419553917/10000000000 : ℝ), (5149927291/10000000000 : ℝ), (-1597920723/10000000000 : ℝ)] ![(46414016457337/100000000000000 : ℝ), (43539056441611/100000000000000 : ℝ), (10046927096723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5419553917/10000000000 : ℝ)|^5071 ≤ (46414016457337/100000000000000 : ℝ)^4047
        have hw : |(5419553917/10000000000 : ℝ)|=(5419553917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5149927291/10000000000 : ℝ)|^5071 ≤ (43539056441611/100000000000000 : ℝ)^4047
        have hw : |(5149927291/10000000000 : ℝ)|=(5149927291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1597920723/10000000000 : ℝ)|^5071 ≤ (10046927096723/100000000000000 : ℝ)^4047
        have hw : |(-1597920723/10000000000 : ℝ)|=(1597920723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1681_box_15 (p : ℝ) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3663843159/10000000000 : ℝ)*x 0 + (4404321161/10000000000 : ℝ)*x 1 + (4404321577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3663843159/10000000000 : ℝ)^5071 ≤ (14209250249497/50000000000000 : ℝ)^4047 := by
    have hnat : (3663843159 : ℕ)^5071*50000000000000^4047 ≤ 14209250249497^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3663843159 10000000000 14209250249497 50000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4404321161/10000000000 : ℝ)^5071 ≤ (35790747623251/100000000000000 : ℝ)^4047 := by
    have hnat : (4404321161 : ℕ)^5071*100000000000000^4047 ≤ 35790747623251^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4404321161 10000000000 35790747623251 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4404321577/10000000000 : ℝ)^5071 ≤ (35790751859149/100000000000000 : ℝ)^4047 := by
    have hnat : (4404321577 : ℕ)^5071*100000000000000^4047 ≤ 35790751859149^4047*10000000000^5071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4404321577 10000000000 35790751859149 100000000000000 5071 4047 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5071/1024 : ℝ)) 5071 4047 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3663843159/10000000000 : ℝ), (4404321161/10000000000 : ℝ), (4404321577/10000000000 : ℝ)] ![(14209250249497/50000000000000 : ℝ), (35790747623251/100000000000000 : ℝ), (35790751859149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3663843159/10000000000 : ℝ)|^5071 ≤ (14209250249497/50000000000000 : ℝ)^4047
        have hw : |(3663843159/10000000000 : ℝ)|=(3663843159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4404321161/10000000000 : ℝ)|^5071 ≤ (35790747623251/100000000000000 : ℝ)^4047
        have hw : |(4404321161/10000000000 : ℝ)|=(4404321161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4404321577/10000000000 : ℝ)|^5071 ≤ (35790751859149/100000000000000 : ℝ)^4047
        have hw : |(4404321577/10000000000 : ℝ)|=(4404321577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1681_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (185410819/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8649/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9737/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(66503/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11543/20000 : ℝ) ∧ (80481/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (22499/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8649/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9737/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8649/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9737/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8649/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9737/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8649/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9737/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8649/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9737/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8649/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9737/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9737/100000 : ℝ) ^ (5063/1024 : ℝ) ≤ (39856045493823/4000000000000000000 : ℝ) := by
    have hpowers : (9737/100000 : ℝ)^5063 ≤ (39856045493823/4000000000000000000 : ℝ)^1024 := by
      have hnat : (9737 : ℕ)^5063*4000000000000000000^1024 ≤ 39856045493823^1024*100000^5063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9737 100000 39856045493823 4000000000000000000 5063 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9737/100000 : ℝ)) (X := (39856045493823/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5063 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8649/50000 : ℝ) ^ (5063/1024 : ℝ) ≤ (3415275194196371/20000000000000000000 : ℝ) := by
    have hpowers : (8649/50000 : ℝ)^5063 ≤ (3415275194196371/20000000000000000000 : ℝ)^1024 := by
      have hnat : (8649 : ℕ)^5063*20000000000000000000^1024 ≤ 3415275194196371^1024*50000^5063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8649 50000 3415275194196371 20000000000000000000 5063 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8649/50000 : ℝ)) (X := (3415275194196371/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5063 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000039856045493823/2000000000000000000 : ℝ) ≤ (10000040304430357/10000000000000000 : ℝ) ^ (5063/1024 : ℝ) := by
    have hpowers : (2000039856045493823/2000000000000000000 : ℝ)^1024 ≤ (10000040304430357/10000000000000000 : ℝ)^5063 := by
      have hnat : (2000039856045493823 : ℕ)^1024*10000000000000000^5063 ≤ 10000040304430357^5063*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000039856045493823 2000000000000000000 10000040304430357 10000000000000000 1024 5063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000040304430357/10000000000000000 : ℝ)) (X := (2000039856045493823/2000000000000000000 : ℝ)) (by norm_num) 5063 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10001807277710832743/10000000000000000000 : ℝ) ≤ (10000365498514947/10000000000000000 : ℝ) ^ (5063/1024 : ℝ) := by
    have hpowers : (10001807277710832743/10000000000000000000 : ℝ)^1024 ≤ (10000365498514947/10000000000000000 : ℝ)^5063 := by
      have hnat : (10001807277710832743 : ℕ)^1024*10000000000000000^5063 ≤ 10000365498514947^5063*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001807277710832743 10000000000000000000 10000365498514947 10000000000000000 1024 5063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000365498514947/10000000000000000 : ℝ)) (X := (10001807277710832743/10000000000000000000 : ℝ)) (by norm_num) 5063 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10003415275194196371/10000000000000000000 : ℝ) ≤ (10000690692599537/10000000000000000 : ℝ) ^ (5063/1024 : ℝ) := by
    have hpowers : (10003415275194196371/10000000000000000000 : ℝ)^1024 ≤ (10000690692599537/10000000000000000 : ℝ)^5063 := by
      have hnat : (10003415275194196371 : ℕ)^1024*10000000000000000^5063 ≤ 10000690692599537^5063*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003415275194196371 10000000000000000000 10000690692599537 10000000000000000 1024 5063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000690692599537/10000000000000000 : ℝ)) (X := (10003415275194196371/10000000000000000000 : ℝ)) (by norm_num) 5063 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(39856045493823/4000000000000000000 : ℝ) ≤ ((75603971912194623617/75610000000000000000 : ℝ)+2*(32519408459/75610000000000 : ℝ)*(9737/100000 : ℝ))^(5063/1024 : ℝ) := by
    rw [show (75603971912194623617/75610000000000000000 : ℝ)+2*(32519408459/75610000000000 : ℝ)*(9737/100000 : ℝ)=(10000040304430357/10000000000000000 : ℝ) by norm_num, show 1+2*(39856045493823/4000000000000000000 : ℝ)=(2000039856045493823/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3415275194196371/20000000000000000000 : ℝ)+(39856045493823/4000000000000000000 : ℝ) ≤ ((75603971912194623617/75610000000000000000 : ℝ)+(32519408459/75610000000000 : ℝ)*((8649/50000 : ℝ)+(9737/100000 : ℝ)))^(5063/1024 : ℝ) := by
    rw [show (75603971912194623617/75610000000000000000 : ℝ)+(32519408459/75610000000000 : ℝ)*((8649/50000 : ℝ)+(9737/100000 : ℝ))=(10000365498514947/10000000000000000 : ℝ) by norm_num, show 1+(3415275194196371/20000000000000000000 : ℝ)+(39856045493823/4000000000000000000 : ℝ)=(10001807277710832743/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3415275194196371/20000000000000000000 : ℝ) ≤ ((75603971912194623617/75610000000000000000 : ℝ)+2*(32519408459/75610000000000 : ℝ)*(8649/50000 : ℝ))^(5063/1024 : ℝ) := by
    rw [show (75603971912194623617/75610000000000000000 : ℝ)+2*(32519408459/75610000000000 : ℝ)*(8649/50000 : ℝ)=(10000690692599537/10000000000000000 : ℝ) by norm_num, show 1+2*(3415275194196371/20000000000000000000 : ℝ)=(10003415275194196371/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (75603971912194623617/75610000000000000000 : ℝ)*(X 1 0+X 2 0)+(32519408459/75610000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5063/1024 : ℝ)) (lo := (9737/100000 : ℝ)) (hi := (8649/50000 : ℝ)) (c := (75603971912194623617/75610000000000000000 : ℝ)) (alpha := (32519408459/75610000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (75603971912194623617/75610000000000000000 : ℝ)*(X 0 1+X 2 1)+(32519408459/75610000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5063/1024 : ℝ)) (lo := (9737/100000 : ℝ)) (hi := (8649/50000 : ℝ)) (c := (75603971912194623617/75610000000000000000 : ℝ)) (alpha := (32519408459/75610000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (75603971912194623617/75610000000000000000 : ℝ)*(X 0 2+X 1 2)+(32519408459/75610000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5063/1024 : ℝ)) (lo := (9737/100000 : ℝ)) (hi := (8649/50000 : ℝ)) (c := (75603971912194623617/75610000000000000000 : ℝ)) (alpha := (32519408459/75610000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-590642523/5000000000 : ℝ)*X 0 0+(5433120533/10000000000 : ℝ)*X 0 1+(1086623349/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((653261327/1250000000 : ℝ)*X 1 0+(-295125853/2000000000 : ℝ)*X 1 1+(5433118661/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2613045969/5000000000 : ℝ)*X 2 0+(27165583/50000000 : ℝ)*X 2 1+(-1475630311/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((283088311/625000000 : ℝ)*X 0 0+(794818889/2000000000 : ℝ)*X 0 1+(1987045441/5000000000 : ℝ)*X 0 2+(283088311/625000000 : ℝ)*X 1 0+(794818889/2000000000 : ℝ)*X 1 1+(1987045441/5000000000 : ℝ)*X 1 2+(283088311/625000000 : ℝ)*X 2 0+(794818889/2000000000 : ℝ)*X 2 1+(1987045441/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1888192287/10000000000 : ℝ)*X 0 0+(5175291999/10000000000 : ℝ)*X 0 1+(5175291623/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((540220293/1000000000 : ℝ)*X 1 0+(-793704659/5000000000 : ℝ)*X 1 1+(1293822929/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5402202729/10000000000 : ℝ)*X 2 0+(2587645929/5000000000 : ℝ)*X 2 1+(-1587409401/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1872041309/5000000000 : ℝ)*X 0 0+(2182939751/5000000000 : ℝ)*X 0 1+(4365879141/10000000000 : ℝ)*X 0 2+(1872041309/5000000000 : ℝ)*X 1 0+(2182939751/5000000000 : ℝ)*X 1 1+(4365879141/10000000000 : ℝ)*X 1 2+(1872041309/5000000000 : ℝ)*X 2 0+(2182939751/5000000000 : ℝ)*X 2 1+(4365879141/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1736707683/10000000000 : ℝ)*X 0 0+(4986597339/10000000000 : ℝ)*X 0 1+(5477070823/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((324754691/625000000 : ℝ)*X 1 0+(-1455712173/10000000000 : ℝ)*X 1 1+(4381657/8000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5196075063/10000000000 : ℝ)*X 2 0+(5477071793/10000000000 : ℝ)*X 2 1+(-363927851/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2329121507/5000000000 : ℝ)*X 0 0+(1953564851/5000000000 : ℝ)*X 0 1+(122097753/312500000 : ℝ)*X 0 2+(2329121507/5000000000 : ℝ)*X 1 0+(1953564851/5000000000 : ℝ)*X 1 1+(122097753/312500000 : ℝ)*X 1 2+(2329121507/5000000000 : ℝ)*X 2 0+(1953564851/5000000000 : ℝ)*X 2 1+(122097753/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-132829321/1000000000 : ℝ)*X 0 0+(87691059/156250000 : ℝ)*X 0 1+(2574963587/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1354888517/2500000000 : ℝ)*X 1 0+(-6391681/40000000 : ℝ)*X 1 1+(5149927489/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5419553917/10000000000 : ℝ)*X 2 0+(5149927291/10000000000 : ℝ)*X 2 1+(-1597920723/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3663843159/10000000000 : ℝ)*X 0 0+(4404321161/10000000000 : ℝ)*X 0 1+(4404321577/10000000000 : ℝ)*X 0 2+(3663843159/10000000000 : ℝ)*X 1 0+(4404321161/10000000000 : ℝ)*X 1 1+(4404321577/10000000000 : ℝ)*X 1 2+(3663843159/10000000000 : ℝ)*X 2 0+(4404321161/10000000000 : ℝ)*X 2 1+(4404321577/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1681_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-66503/100000 : ℝ) ≤ (-1257032237772157623903986256088371/1890250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (25610117/100000000000000 : ℝ)*(lower0) + (11829317/50000000000000 : ℝ)*(upper3) + (24580239/100000000000000 : ℝ)*(lower4) + (641105804458507/50000000000000 : ℝ)*(major0) + (641105804458507/50000000000000 : ℝ)*(major1) + (641105804458507/50000000000000 : ℝ)*(major2) + (1810858857/100000000000000 : ℝ)*(sp1) + (208748363/20000000000000 : ℝ)*(sp2) + (947518576326923/50000000000000 : ℝ)*(sp4) + (1895036688940337/100000000000000 : ℝ)*(sp5) + (1895037456057379/100000000000000 : ℝ)*(sp6) + (691551378680711/100000000000000 : ℝ)*(sp7) + (1347145347/100000000000000 : ℝ)*(sp8) + (14397739/5000000000000 : ℝ)*(sp15) + (691551666635491/100000000000000 : ℝ)*(f.failure) + (947519249899597/50000000000000 : ℝ)*(f.sum) + (19330652691163/7561000000000000000000000000 : ℝ)*base66 + (35881451714007259819/3780500000000000000000000000000000 : ℝ)*base67 + (42336335403096759819/3780500000000000000000000000000000 : ℝ)*base69 + (2187331684501759819/3780500000000000000000000000000000 : ℝ)*base71 + (14931031221261/7561000000000000000000000000 : ℝ)*base73 + (14051631963631759819/3780500000000000000000000000000000 : ℝ)*base75 + (7727270944362259819/3780500000000000000000000000000000 : ℝ)*base77 + (20406582131209759819/3780500000000000000000000000000000 : ℝ)*base79 + (6212049981093/1512200000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (39222871/10000000000000000000000 : ℝ)*base90 + (39222871/10000000000000000000000 : ℝ)*base92 + (39222871/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (11543/20000 : ℝ) ≤ (68187583215442829688278657551911/118140625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (130905973/100000000000000 : ℝ)*(upper3) + (73983467/50000000000000 : ℝ)*(upper4) + (134608467/50000000000000 : ℝ)*(lower5) + (21541924089657/1562500000000 : ℝ)*(major0) + (21541924089657/1562500000000 : ℝ)*(major1) + (21541924089657/1562500000000 : ℝ)*(major2) + (498633027598527/25000000000000 : ℝ)*(sp0) + (39890732288381/2000000000000 : ℝ)*(sp1) + (997271592375967/50000000000000 : ℝ)*(sp2) + (743577622747807/100000000000000 : ℝ)*(sp3) + (3834762091/50000000000000 : ℝ)*(sp5) + (549595649/50000000000000 : ℝ)*(sp6) + (5275582439/100000000000000 : ℝ)*(sp7) + (12173549123/100000000000000 : ℝ)*(sp8) + (743582898330247/100000000000000 : ℝ)*(f.failure) + (31164754436613/1562500000000 : ℝ)*(f.sum) + (48623276573187/7561000000000000000000000000 : ℝ)*base65 + (80895838974901881/118140625000000000000000000000000 : ℝ)*base68 + (1006898543320598119/118140625000000000000000000000000 : ℝ)*base69 + (394611169608848119/118140625000000000000000000000000 : ℝ)*base71 + (7637394109823/7561000000000000000000000000 : ℝ)*base74 + (129505150257541247/59070312500000000000000000000000 : ℝ)*base75 + (234758365488316869/118140625000000000000000000000000 : ℝ)*base77 + (4694224506394883/3691894531250000000000000000000 : ℝ)*base80 + (59035009899803/7561000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (28742293/10000000000000000000000 : ℝ)*base89 + (28742293/10000000000000000000000 : ℝ)*base91 + (28742293/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (80481/100000 : ℝ) ≤ (6085378533183467879367075591/7561000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27847789/100000000000000 : ℝ)*(upper2) + (19670623/25000000000000 : ℝ)*(upper3) + (199516519/100000000000000 : ℝ)*(upper4) + (1414209592731701/100000000000000 : ℝ)*(major0) + (1414209592731701/100000000000000 : ℝ)*(major1) + (1414209592731701/100000000000000 : ℝ)*(major2) + (145137/100000000000000 : ℝ)*(sp0) + (1905901451/100000000000000 : ℝ)*(sp1) + (29310547271/50000000000000 : ℝ)*(sp2) + (48802483/400000000000 : ℝ)*(sp3) + (20388474232241/1000000000000 : ℝ)*(sp8) + (407769103493557/20000000000000 : ℝ)*(sp9) + (1019394401137347/50000000000000 : ℝ)*(sp10) + (762731635126883/100000000000000 : ℝ)*(sp11) + (762743835747633/100000000000000 : ℝ)*(f.failure) + (509711855842309/25000000000000 : ℝ)*(f.sum) + (8488396071921/3780500000000000000000000000 : ℝ)*base66 + (23788340528938817483/7561000000000000000000000000000000 : ℝ)*base68 + (14227769426205182517/7561000000000000000000000000000000 : ℝ)*base69 + (10335594604099817483/7561000000000000000000000000000000 : ℝ)*base72 + (2434252471269/3780500000000000000000000000 : ℝ)*base74 + (10339109351449182517/7561000000000000000000000000000000 : ℝ)*base75 + (9106201272961817483/7561000000000000000000000000000000 : ℝ)*base78 + (3588258940680182517/7561000000000000000000000000000000 : ℝ)*base79 + (6594084202347/1890250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (11841427/10000000000000000000000 : ℝ)*base89 + (11841427/10000000000000000000000 : ℝ)*base91 + (11841427/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-22499/25000 : ℝ) ≤ (-1701110025070527663171498016015593/1890250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (49085563/50000000000000 : ℝ)*(upper3) + (18893079/20000000000000 : ℝ)*(lower4) + (33030317/50000000000000 : ℝ)*(upper5) + (730185188080957/50000000000000 : ℝ)*(major0) + (730185188080957/50000000000000 : ℝ)*(major1) + (730185188080957/50000000000000 : ℝ)*(major2) + (193910959/10000000000000 : ℝ)*(sp4) + (2756005249/20000000000000 : ℝ)*(sp5) + (24699324033/50000000000000 : ℝ)*(sp6) + (14115706159/50000000000000 : ℝ)*(sp7) + (27038705766879/1250000000000 : ℝ)*(sp12) + (432616924086733/20000000000000 : ℝ)*(sp13) + (540762250452961/25000000000000 : ℝ)*(sp14) + (787612092943249/100000000000000 : ℝ)*(sp15) + (787640324355567/100000000000000 : ℝ)*(f.failure) + (216309840045991/10000000000000 : ℝ)*(f.sum) + (7517917605867/7561000000000000000000000000 : ℝ)*base65 + (22492632937724338531/3780500000000000000000000000000000 : ℝ)*base68 + (9552600252442661469/3780500000000000000000000000000000 : ℝ)*base69 + (10370129763489338531/3780500000000000000000000000000000 : ℝ)*base72 + (21673727140913/7561000000000000000000000000 : ℝ)*base74 + (4011997651134838531/3780500000000000000000000000000000 : ℝ)*base76 + (6635630857245338531/3780500000000000000000000000000000 : ℝ)*base78 + (2616606893464661469/3780500000000000000000000000000000 : ℝ)*base79 + (30693756832739/7561000000000000000000000000 : ℝ)*base81 + (75320627/10000000000000000000000 : ℝ)*base90 + (75320627/10000000000000000000000 : ℝ)*base92 + (75320627/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1681_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (185410819/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8649/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9737/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66503/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11543/20000 : ℝ) else (80481/100000 : ℝ) ≤ X j i ∧ X j i ≤ (22499/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1681_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1681_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (185410819/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1733/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (971/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66503/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11543/20000 : ℝ) else (80481/100000 : ℝ) ≤ X j i ∧ X j i ≤ (22499/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1681_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1681_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1681_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5063/1024 : ℝ) ≤ p) (hpb : p ≤ (5071/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (185410819/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1733/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (971/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66503/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11543/20000 : ℝ) else (80481/100000 : ℝ) ≤ X j i ∧ X j i ≤ (22499/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1681_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
