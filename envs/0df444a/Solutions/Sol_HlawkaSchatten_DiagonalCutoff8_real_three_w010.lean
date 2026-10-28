-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff8.real_three_w010
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T15:33:04.560146+00:00
-- url     : https://prove2.me/submissions/e643edfe-41de-48d2-89cf-305de5182ed5

import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Normalization
import Mathlib.Tactic.Abel
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Ring
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Coordinates
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Mathlib.Tactic.FinCases
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_NormHessian
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxGeometry
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxCoordinates
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.GCongr
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxConvexity
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxHessian
import Mathlib.Topology.Order.Compact
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_coarse_failure_reduction
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_nonnegative_of_curvature_margins
/- Generic norm, Bernoulli, permutation, and curvature arguments retain
the Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.
The cutoff-8 geometry and all rational certificates are proved below. -/
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
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
namespace HlawkaSchatten.DiagonalConstruction
variable {ι : Type*} [Fintype ι]
theorem hlawkaDeficit_eq (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K x y z =
      K * pairGapSum (lpNorm p) x y z - tripleGap (lpNorm p) x y z := by
  unfold hlawkaDeficit pairGapSum pairGap tripleGap
  ring
end HlawkaSchatten.DiagonalConstruction
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
namespace HlawkaSchatten.DiagonalCutoff16Scalar
theorem two_tail_norm_bound (m : ℕ) (hm : 1 ≤ m)
    {p S y1 y2 rho cap eps : ℝ}
    (hp : (m : ℝ) ≤ p) (hS : 0 ≤ S) (hScap : S ≤ cap) (hcap : 0 < cap)
    (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1) (heps : 0 ≤ eps)
    (hy1 : |y1| ≤ rho * S) (hy2 : |y2| ≤ rho * S)
    (hcert : 2 * rho ^ m * cap ≤ (m : ℝ) * eps) :
    (|S| ^ p + |y1| ^ p + |y2| ^ p) ^ (1 / p) ≤ S + eps := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hp1 : 1 ≤ p := hm1.trans hp
  have hp0 : 0 < p := by linarith
  rcases eq_or_lt_of_le hS with hS0 | hSpos
  · have hzero : S = 0 := hS0.symm
    subst S
    have hy10 : y1 = 0 := abs_nonpos_iff.mp (by simpa using hy1)
    have hy20 : y2 = 0 := abs_nonpos_iff.mp (by simpa using hy2)
    subst y1 y2
    simpa [Real.zero_rpow hp0.ne', Real.zero_rpow (inv_ne_zero hp0.ne')] using heps
  · rw [abs_of_pos hSpos]
    have hpow : rho ^ p ≤ rho ^ m := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge' hrho hrho1 (by positivity) hp
    have hy (y : ℝ) (hy : |y| ≤ rho * S) :
        |y| ^ p ≤ rho ^ m * S ^ p := by
      calc
        _ ≤ (rho * S) ^ p := Real.rpow_le_rpow (abs_nonneg _) hy hp0.le
        _ = rho ^ p * S ^ p := Real.mul_rpow hrho hSpos.le
        _ ≤ _ := mul_le_mul_of_nonneg_right hpow (by positivity)
    have hnum : 2 * rho ^ m ≤ p * (eps / S) := by
      have h1 : 2 * rho ^ m ≤ (m : ℝ) * eps / cap := (le_div_iff₀ hcap).2 hcert
      have h2 : eps / cap ≤ eps / S := div_le_div_of_nonneg_left heps hSpos hScap
      have h3 := mul_le_mul hp h2 (div_nonneg heps hcap.le) (by positivity : (0 : ℝ) ≤ p)
      calc
        _ ≤ (m : ℝ) * eps / cap := h1
        _ = (m : ℝ) * (eps / cap) := by ring
        _ ≤ p * (eps / S) := h3
    have hbern : 1 + p * (eps / S) ≤ (1 + eps / S) ^ p :=
      one_add_mul_self_le_rpow_one_add (by have := div_nonneg heps hSpos.le; linarith) hp1
    have heq : (S + eps) ^ p = S ^ p * (1 + eps / S) ^ p := by
      rw [← Real.mul_rpow hSpos.le (by positivity)]
      congr 1
      field_simp
    have h1 := hy y1 hy1
    have h2 := hy y2 hy2
    have h3 := mul_le_mul_of_nonneg_right hnum (show 0 ≤ S ^ p by positivity)
    have h4 := mul_le_mul_of_nonneg_left hbern (show 0 ≤ S ^ p by positivity)
    have hsum : S ^ p + |y1| ^ p + |y2| ^ p ≤ (S + eps) ^ p := by
      rw [heq]
      nlinarith
    calc
      _ ≤ ((S + eps) ^ p) ^ (1 / p) := Real.rpow_le_rpow (by positivity) hsum (by positivity)
      _ = S + eps := by rw [one_div, Real.rpow_rpow_inv (by positivity) hp0.ne']
theorem root_transfer_upper {m p B b A : ℝ} (hm : 0 < m) (hp : m ≤ p)
    (hB : 0 ≤ B) (hBb : B ≤ b) (hb : b ≤ A^m) (hA : 1 ≤ A) :
    B^(1/p) ≤ 1+(m/p)*(A-1) := by
  have hp0 : 0 < p := hm.trans_le hp
  have hmp : 0 ≤ m/p := div_nonneg hm.le hp0.le
  have hbase : 0 ≤ 1+(m/p)*(A-1) := by positivity
  have hratio : 1 ≤ p/m := (le_div_iff₀ hm).mpr (by simpa using hp)
  have hb0 := one_add_mul_self_le_rpow_one_add
    (show -1 ≤ (m/p)*(A-1) by
      have hnon := mul_nonneg hmp (sub_nonneg.mpr hA)
      linarith) hratio
  have hroot : A ≤ (1+(m/p)*(A-1))^(p/m) := by
    convert hb0 using 1 <;> field_simp <;> ring
  have hpow : A^m ≤ (1+(m/p)*(A-1))^p := by
    have h := Real.rpow_le_rpow (by linarith : 0 ≤ A) hroot hm.le
    rw [← Real.rpow_mul hbase] at h
    convert h using 1 <;> field_simp
  calc
    _ ≤ ((1+(m/p)*(A-1))^p)^(1/p) :=
      Real.rpow_le_rpow hB (hBb.trans (hb.trans hpow)) (by positivity)
    _ = _ := by rw [one_div, Real.rpow_rpow_inv hbase hp0.ne']
theorem cyclicB_lower_two {p t : ℝ} (hp : 0 < p) : 2 ≤ cyclicB p t := by
  have h : (2 : ℝ)^p ≤ 2*|1-t|^p+2^p := by
    have := Real.rpow_nonneg (abs_nonneg (1-t)) p
    linarith
  calc
    (2 : ℝ) = (2^p)^(1/p) := by rw [one_div, Real.rpow_rpow_inv (by norm_num) hp.ne']
    _ ≤ cyclicB p t := Real.rpow_le_rpow (by positivity) h (by positivity)
end HlawkaSchatten.DiagonalCutoff16Scalar
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten.DiagonalCutoff16Scalar
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalCutoff8Scalar

theorem root_lower_from_log {p B c : ℝ} (hp : 0 < p) (hB : 0 < B)
    (hc : c ≤ Real.log B) : 1+c/p ≤ B^(1/p) := by
  rw [Real.rpow_def_of_pos hB]
  have h := Real.add_one_le_exp (Real.log B*(1/p))
  have hm := mul_le_mul_of_nonneg_right hc (one_div_nonneg.mpr hp.le)
  calc
    1+c/p = c*(1/p)+1 := by ring
    _ ≤ Real.log B*(1/p)+1 := by linarith only [hm]
    _ ≤ _ := h

theorem root_bounds8 {p : ℝ} (hp : 8 ≤ p) :
    1+(693/1000 : ℝ)/p ≤ (2 : ℝ)^(1/p) ∧
    1+1/p ≤ (3 : ℝ)^(1/p) ∧ (3 : ℝ)^(1/p) ≤ 3 := by
  have hp0 : 0 < p := by linarith
  refine ⟨root_lower_from_log hp0 (by norm_num) (by linarith [Real.log_two_gt_d9]),
    root_lower_from_log hp0 (by norm_num) (by linarith [Real.log_three_gt_d9]), ?_⟩
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
    ((div_le_one hp0).mpr (show (1 : ℝ) ≤ p by linarith))
  simpa using h

theorem cyclicB_upper8 {p t : ℝ} (hp : 8 ≤ p)
    (ht : t ∈ Set.Icc (1/2 : ℝ) 2) : cyclicB p t ≤ 2+1/500 := by
  have hy : |1-t| ≤ (1/2 : ℝ)*2 := abs_le.mpr ⟨by linarith [ht.1,ht.2],by linarith [ht.1,ht.2]⟩
  have h := two_tail_norm_bound (cap := (2 : ℝ)) 8 (by norm_num) hp
    (by norm_num : (0 : ℝ) ≤ 2) le_rfl (by norm_num)
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num) (by norm_num : (0 : ℝ) ≤ 1/500)
    hy hy (by norm_num)
  have he : (|2|^p+|1-t|^p+|1-t|^p : ℝ) = 2*|1-t|^p+2^p := by
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)];ring
  rw [he] at h
  exact h

theorem cyclicA_lower8 {p t : ℝ} (hp : 8 ≤ p)
    (ht : t ∈ Set.Icc (1/2 : ℝ) 2) :
    (2 : ℝ)^(1/p) ≤ cyclicA p t ∧ t ≤ cyclicA p t := by
  have hp0 : 0 < p := by linarith
  have ht0 : 0 ≤ t := by linarith [ht.1]
  constructor
  · exact Real.rpow_le_rpow (by norm_num)
      (show (2 : ℝ) ≤ t^p+2 by linarith [Real.rpow_nonneg ht0 p]) (by positivity)
  · calc
      t = (t^p)^(1/p) := by rw [one_div, Real.rpow_rpow_inv ht0 hp0.ne']
      _ ≤ cyclicA p t := Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)

theorem cyclicA_lower_large_t8 {p t : ℝ} (hp : 8 ≤ p) (hp16 : p ≤ 12)
    (ht : 9/10 ≤ t) : 1+(4/5 : ℝ)/p ≤ cyclicA p t := by
  have hp0 : 0 < p := by linarith
  have hl : (4/5 : ℝ) ≤ Real.log (9/4) := by
    have he : Real.log (9/4 : ℝ) = 2*(Real.log 3-Real.log 2) := by
      rw [show (9/4 : ℝ) = (3/2 : ℝ)^2 by norm_num, Real.log_pow,
        Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num
    rw [he]
    linarith [Real.log_three_gt_d9,Real.log_two_lt_d9]
  have htp : (9/10 : ℝ)^12 ≤ t^p := by
    have h1 := Real.rpow_le_rpow_of_exponent_ge' (by norm_num : (0 : ℝ) ≤ 9/10)
      (by norm_num) hp0.le hp16
    have h2 := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 9/10) ht hp0.le
    norm_num at h1
    norm_num
    exact h1.trans h2
  have hbase : (9/4 : ℝ) ≤ t^p+2 := by norm_num at htp ⊢;linarith
  exact (root_lower_from_log hp0 (by norm_num) hl).trans
    (Real.rpow_le_rpow (by norm_num) hbase (one_div_nonneg.mpr hp0.le))

theorem cyclic_minimum_lower8 {p t : ℝ} (hp : 8 ≤ p) (hp16 : p ≤ 12)
    (ht : t ∈ Set.Icc (1/2 : ℝ) 2) :
    2*p+1/40 ≤ 2*(p-1)*cyclicA p t+(2/3)*(3 : ℝ)^(1/p)*(2-t) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hb,ha,haU⟩ := root_bounds8 hp
  obtain ⟨hAb,hAt⟩ := cyclicA_lower8 hp ht
  set z := 1/p with hz
  have hz0 : 0 ≤ z := by positivity
  have hz12 : z ≤ 1/8 := one_div_le_one_div_of_le (by norm_num) hp
  have hpz : p*z = 1 := mul_one_div_cancel hp0.ne'
  have hpz2 : p*z^2 = z := by calc _ = (p*z)*z := by ring
                                               _ = z := by rw [hpz];ring
  have hz2 : z^2 ≤ (1/8 : ℝ)^2 := by nlinarith
  have ha0 : 0 ≤ (3 : ℝ)^(1/p) := by positivity
  by_cases ht0 : t ≤ 9/10
  · have hA : 1+(693/1000 : ℝ)*z ≤ cyclicA p t := by
      have h := hb.trans hAb
      simpa only [z,div_eq_mul_inv,one_mul] using h
    have h1 := mul_le_mul_of_nonneg_left hA (show 0 ≤ 2*(p-1) by linarith)
    have h2 := mul_le_mul ha (show (11/10 : ℝ) ≤ 2-t by linarith)
      (by norm_num) ha0
    change 1+z ≤ (3 : ℝ)^(1/p) at ha
    nlinarith
  · have hA := cyclicA_lower_large_t8 (t := t) hp hp16 (by linarith)
    have hA' : 1+(4/5 : ℝ)*z ≤ cyclicA p t := by
      simpa only [z,div_eq_mul_inv,one_mul] using hA
    have hmul := mul_le_mul_of_nonneg_right ha (show 0 ≤ 1-(4/5 : ℝ)*z by linarith)
    change (1+z)*(1-(4/5 : ℝ)*z) ≤ (3 : ℝ)^(1/p)*(1-(4/5 : ℝ)*z) at hmul
    have hmin : 2*p+1/40 ≤ 2*(p-1)*(1+(4/5 : ℝ)*z)+
        (2/3)*(3 : ℝ)^(1/p)*(1-(4/5 : ℝ)*z) := by nlinarith
    by_cases htb : t ≤ 1+(4/5 : ℝ)*z
    · have h1 := mul_nonneg (show 0 ≤ p-1 by linarith) (sub_nonneg.mpr hA')
      have h2 := mul_nonneg ha0 (sub_nonneg.mpr htb)
      nlinarith
    · have h1 := mul_nonneg (show 0 ≤ p-1 by linarith) (sub_nonneg.mpr hAt)
      have h2 := mul_nonneg (show 0 ≤ p-1-(3 : ℝ)^(1/p)/3 by linarith)
        (show 0 ≤ t-(1+(4/5 : ℝ)*z) by linarith)
      nlinarith

theorem cyclicRatio_upper8 {p t : ℝ} (hp : 8 ≤ p) (hp16 : p ≤ 12)
    (ht : t ∈ Set.Icc (1/2 : ℝ) 2) : cyclicRatio p t ≤ p/2 := by
  have hp0 : 0 < p := by linarith
  have hB := cyclicB_upper8 hp ht
  have hm := cyclic_minimum_lower8 hp hp16 ht
  have hA := (root_bounds8 hp).1.trans (cyclicA_lower8 hp ht).1
  have hA' : 1+(693/1000 : ℝ)*(1/p) ≤ cyclicA p t := by
    simpa only [div_eq_mul_inv,one_mul] using hA
  have hinv : (1/12 : ℝ) ≤ 1/p := one_div_le_one_div_of_le hp0 hp16
  have hden : 0 < 6*cyclicA p t-3*cyclicB p t := by nlinarith only [hA',hinv,hB]
  have hmB := mul_le_mul_of_nonneg_left hB hp0.le
  unfold cyclicRatio
  rw [abs_of_nonneg (show 0 ≤ 2-t by linarith [ht.2]),div_le_iff₀ hden]
  nlinarith

theorem cyclicConstant_upper8 {p : ℝ} (hp : 8 ≤ p) (hp16 : p ≤ 12) :
    cyclicConstant p ≤ p/2 := by
  unfold cyclicConstant
  apply csSup_le
  · exact ⟨cyclicRatio p 1,1,by norm_num,rfl⟩
  · rintro y ⟨t,ht,rfl⟩
    exact cyclicRatio_upper8 hp hp16 ht


theorem cyclic_denominator_positive8 {p t : ℝ} (hp : 8 ≤ p) (hp16 : p ≤ 12)
    (ht : t ∈ Set.Icc (1/2 : ℝ) 2) : 0 < 6*cyclicA p t-3*cyclicB p t := by
  have hp0 : 0 < p := by linarith
  have hB := cyclicB_upper8 hp ht
  have hA := (root_bounds8 hp).1.trans (cyclicA_lower8 hp ht).1
  have hA' : 1+(693/1000 : ℝ)*(1/p) ≤ cyclicA p t := by
    simpa only [div_eq_mul_inv,one_mul] using hA
  have hinv : (1/12 : ℝ) ≤ 1/p := one_div_le_one_div_of_le hp0 hp16
  nlinarith only [hA',hinv,hB]

theorem cyclicRatio_lower_endpoint {p alpha beta c t Aup aup : ℝ}
    (hp : 8 ≤ p) (hp16 : p ≤ 12) (ha : 0 < alpha)
    (hap : alpha ≤ p) (hpb : p ≤ beta) (hc : 0 < c) (hcp : 1 ≤ 2*c*p)
    (ht0 : 1/2 ≤ t) (ht1 : t ≤ 1) (hAup : 1 ≤ Aup) (haup : 1 ≤ aup)
    (hAend : t^alpha+2 ≤ Aup^alpha) (haend : (3 : ℝ) ≤ aup^alpha)
    (hH : 0 ≤ 3*(Aup-1)-(2-t)*(aup-1))
    (hcheck : 0 < 3-(2-t)+(alpha/beta)*(3*(Aup-1)-(2-t)*(aup-1))-6*c*alpha*(Aup-1)) :
    c*p < cyclicRatio p t := by
  have hp0 : 0 < p := by linarith
  have htpos : 0 < t := by linarith
  have htp : t^p ≤ t^alpha := Real.rpow_le_rpow_of_exponent_ge htpos ht1 hap
  have hAp : cyclicA p t ≤ 1+(alpha/p)*(Aup-1) := by
    exact root_transfer_upper ha hap (by positivity) (by linarith) hAend hAup
  have hap' : (3 : ℝ)^(1/p) ≤ 1+(alpha/p)*(aup-1) :=
    root_transfer_upper ha hap (by norm_num) le_rfl haend haup
  have hB := cyclicB_lower_two (t := t) hp0
  have hden := cyclic_denominator_positive8 hp hp16 (show t ∈ Set.Icc (1/2 : ℝ) 2 by exact ⟨ht0,by linarith⟩)
  have hmono := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_left ha.le hp0 hpb) hH
  have hpos : 0 < 3-(2-t)+(alpha/p)*(3*(Aup-1)-(2-t)*(aup-1))-6*c*alpha*(Aup-1) := by linarith
  have h1 := mul_le_mul_of_nonneg_left hAp (show 0 ≤ 6*c*p-3 by linarith)
  have h2 := mul_le_mul_of_nonneg_left hap' (show 0 ≤ 2-t by linarith)
  have heq : (6*c*p-3)*(1+(alpha/p)*(Aup-1))+(2-t)*(1+(alpha/p)*(aup-1)) =
      6*c*p-(3-(2-t)+(alpha/p)*(3*(Aup-1)-(2-t)*(aup-1))-6*c*alpha*(Aup-1)) := by
    field_simp
    ring
  have h3 := mul_le_mul_of_nonneg_left hB (show 0 ≤ 3*c*p by positivity)
  unfold cyclicRatio
  rw [abs_of_nonneg (show 0 ≤ 2-t by linarith), lt_div_iff₀ hden]
  nlinarith

theorem cyclicConstant_lower_endpoint {p alpha beta c t Aup aup : ℝ}
    (hp : 8 ≤ p) (hp16 : p ≤ 12) (ha : 0 < alpha)
    (hap : alpha ≤ p) (hpb : p ≤ beta) (hc : 0 < c) (hcp : 1 ≤ 2*c*p)
    (ht0 : 1/2 ≤ t) (ht1 : t ≤ 1) (hAup : 1 ≤ Aup) (haup : 1 ≤ aup)
    (hAend : t^alpha+2 ≤ Aup^alpha) (haend : (3 : ℝ) ≤ aup^alpha)
    (hH : 0 ≤ 3*(Aup-1)-(2-t)*(aup-1))
    (hcheck : 0 < 3-(2-t)+(alpha/beta)*(3*(Aup-1)-(2-t)*(aup-1))-6*c*alpha*(Aup-1)) :
    c*p < cyclicConstant p := by
  have hratio := cyclicRatio_lower_endpoint hp hp16 ha hap hpb hc hcp ht0 ht1 hAup haup hAend haend hH hcheck
  have hbounded : BddAbove (cyclicRatio p '' Set.Icc (1/2 : ℝ) 2) := by
    refine ⟨p/2, ?_⟩
    rintro y ⟨s,hs,rfl⟩
    exact cyclicRatio_upper8 hp hp16 hs
  have ht : t ∈ Set.Icc (1/2 : ℝ) 2 := ⟨ht0,by linarith⟩
  exact hratio.trans_le (le_csSup hbounded (Set.mem_image_of_mem (cyclicRatio p) ht))

end HlawkaSchatten.DiagonalCutoff8Scalar

/- Bernoulli envelope transport, generalized from accepted submission 6ad9b901-e3db-45c8-84cd-c4345b3b35df (Yuxuan Xu, Apache-2.0) to real lower endpoints. -/
open HlawkaSchatten.DiagonalConstruction
set_option autoImplicit false
namespace HlawkaSchatten.DiagonalCutoff16Scalar
theorem bernoulli_scale (m : ℝ) (hm : 1 ≤ m) {p d : ℝ}
    (hp : m ≤ p) (hd : 0 ≤ d) (hdm : d < m) :
    (1-d/m)^m ≤ (1-d/p)^p := by
  have hm0 : (0 : ℝ) < m := by linarith
  have hp0 : 0 < p := hm0.trans_le hp
  have hbase : 0 ≤ 1-d/p := by
    apply sub_nonneg.mpr
    exact (div_le_one hp0).mpr (by linarith)
  have he : (1 : ℝ) ≤ p/m := (le_div_iff₀ hm0).mpr (by simpa using hp)
  have hs : -1 ≤ -d/p := by
    have h := (div_le_one hp0).mpr (show d ≤ p by linarith)
    simpa only [neg_div] using neg_le_neg h
  have hb := one_add_mul_self_le_rpow_one_add hs he
  have hroot : 1-d/m ≤ (1-d/p)^(p/m) := by
    convert hb using 1 <;> field_simp <;> ring
  calc
    _ ≤ ((1-d/p)^(p/m))^m := Real.rpow_le_rpow
      (by apply sub_nonneg.mpr; exact (div_le_one hm0).mpr hdm.le) hroot hm0.le
    _ = (1-d/p)^p := by
      rw [← Real.rpow_mul hbase]
      congr 1
      field_simp

theorem envelope_linear_of_certificate (m : ℝ) (hm : 1 ≤ m)
    {p q c : ℝ} (hp : m ≤ p) (hq : 0 ≤ q) (hq1 : q < 1) (hc : 0 < c)
    (hdm : (1-q)/(2*c) < m)
    (hcert : (1+q^m)/2 < (1-((1-q)/(2*c))/m)^m) :
    scalarEnvelope p q < c*p := by
  have hm0 : (0 : ℝ) < m := by linarith
  have hp0 : 0 < p := hm0.trans_le hp
  set d := (1-q)/(2*c) with hd_def
  have hd : 0 ≤ d := div_nonneg (by linarith) (by positivity)
  have hscale := bernoulli_scale m hm hp hd hdm
  have hqpow : q^p ≤ q^m := by
    exact Real.rpow_le_rpow_of_exponent_ge' hq hq1.le (by positivity) hp
  have hg0 : 0 ≤ scalarEnvelopeRoot p q := Real.rpow_nonneg (by positivity) _
  have hgpow : scalarEnvelopeRoot p q ^ p = (1+q^p)/2 := by
    unfold scalarEnvelopeRoot
    rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hp0.ne', Real.rpow_one]
  have hb0 : 0 ≤ 1-d/p := by
    apply sub_nonneg.mpr
    exact (div_le_one hp0).mpr (by linarith)
  have hpow : scalarEnvelopeRoot p q ^ p < (1-d/p)^p := by
    rw [hgpow]
    exact (show (1+q^p)/2 < (1-d/m)^m by linarith).trans_le hscale
  have hg : scalarEnvelopeRoot p q < 1-d/p :=
    (Real.rpow_lt_rpow_iff hg0 hb0 hp0).mp hpow
  have hgap : 0 < 2*(1-scalarEnvelopeRoot p q) := by
    have := div_nonneg hd hp0.le
    linarith
  have hdp : d < p*(1-scalarEnvelopeRoot p q) := by
    have ht : d/p < 1-scalarEnvelopeRoot p q := by linarith
    have hm := (div_lt_iff₀ hp0).mp ht
    simpa only [mul_comm] using hm
  have hmul := mul_lt_mul_of_pos_left hdp (show 0 < 2*c by positivity)
  have heq : 2*c*d = 1-q := by rw [hd_def]; field_simp
  unfold scalarEnvelope
  apply (div_lt_iff₀ hgap).mpr
  nlinarith

end HlawkaSchatten.DiagonalCutoff16Scalar

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

namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten.DiagonalConstruction
def offsum (X : Triple) : ℝ := X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1
def conjugate (e : Equiv.Perm (Fin 3)) (X : Triple) : Triple := fun j i => X (e j) (e i)
theorem totalTriple_eq (X : Triple) : totalTriple X = X 0 + X 1 + X 2 := by
  simp [totalTriple, Fin.sum_univ_three]
theorem offsum_eq_sum (X : Triple) :
    offsum X = ∑ j, ∑ i, if j = i then (0 : ℝ) else X j i := by
  simp [offsum, Fin.sum_univ_three]
  ring
theorem offsum_conjugate (e : Equiv.Perm (Fin 3)) (X : Triple) :
    offsum (conjugate e X) = offsum X := by
  rw [offsum_eq_sum, offsum_eq_sum]
  calc
    _ = ∑ j, ∑ i, if e j = e i then (0 : ℝ) else X (e j) (e i) := by
      simp only [conjugate, e.injective.eq_iff]
    _ = ∑ j, ∑ i, if e j = i then (0 : ℝ) else X (e j) i := by
      apply Finset.sum_congr rfl
      intro j _
      exact Equiv.sum_comp e (fun i ↦ if e j = i then (0 : ℝ) else X (e j) i)
    _ = _ := Equiv.sum_comp e (fun j ↦ ∑ i, if j = i then (0 : ℝ) else X j i)
theorem totalTriple_conjugate (e : Equiv.Perm (Fin 3)) (X : Triple) :
    totalTriple (conjugate e X) = totalTriple X ∘ e := by
  ext i
  change (∑ j, X (e j) (e i)) = ∑ j, X j (e i)
  exact Equiv.sum_comp e (fun j ↦ X j (e i))
end HlawkaSchatten.DiagonalRealBundle
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
set_option autoImplicit false
namespace HlawkaSchatten.DiagonalCutoff12
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle

theorem coordinateBox_of_base_bounds {p k B A ell u v w : ℝ}
    (base : ∀ Y : Fin 3 → Fin 3 → ℝ,
      lpNorm p (Y 0)+lpNorm p (Y 1)+lpNorm p (Y 2) ≤ 3 →
      lpNorm p (Y 0+Y 1+Y 2) ≤ A →
      lpNorm p (Y 0+Y 1+Y 2) ≤ k*offsum Y+B →
      -u ≤ Y 0 0 ∧ Y 0 0 ≤ -ell ∧ v ≤ Y 0 1 ∧ Y 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ)
    (hS : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2) ≤ 3)
    (hT : lpNorm p (X 0+X 1+X 2) ≤ A)
    (hC : lpNorm p (X 0+X 1+X 2) ≤ k*offsum X+B) :
    ∀ j i, if j = i then -u ≤ X j i ∧ X j i ≤ -ell
      else v ≤ X j i ∧ X j i ≤ w := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      -u ≤ X (e 0) (e 0) ∧ X (e 0) (e 0) ≤ -ell ∧
      v ≤ X (e 0) (e 1) ∧ X (e 0) (e 1) ≤ w := by
    have hr (j : Fin 3) : lpNorm p (conjugate e X j) = lpNorm p (X (e j)) := by
      exact lpNorm_comp_equiv p (X (e j)) e
    have hnorm : lpNorm p (conjugate e X 0)+lpNorm p (conjugate e X 1)+
        lpNorm p (conjugate e X 2) = lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2) := by
      rw [hr,hr,hr]
      simpa [Fin.sum_univ_three] using Equiv.sum_comp e (fun j => lpNorm p (X j))
    have ht : lpNorm p (conjugate e X 0+conjugate e X 1+conjugate e X 2) =
        lpNorm p (X 0+X 1+X 2) := by
      rw [← totalTriple_eq, totalTriple_conjugate, lpNorm_comp_equiv, totalTriple_eq]
    have h := base (conjugate e X) (by rwa [hnorm]) (by rwa [ht])
      (by rwa [ht,offsum_conjugate])
    exact h
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

end HlawkaSchatten.DiagonalCutoff12
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalCutoff12
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators

theorem norm_cap_of_power_budget {p a U : ℝ} (hp : 0 < p) (ha : 0 ≤ a)
    (hap : a ≤ p) (hU : 0 ≤ U) (b x : Fin 3 → ℝ)
    (hb0 : ∀ i, 0 ≤ b i) (hb1 : ∀ i, b i ≤ 1)
    (hx : ∀ i, |x i| ≤ U*b i) (hbudget : (∑ i, (b i)^a) ≤ 1) :
    lpNorm p x ≤ U := by
  have hs : (∑ i, (b i)^p) ≤ 1 :=
    (Finset.sum_le_sum fun i _ => Real.rpow_le_rpow_of_exponent_ge'
      (hb0 i) (hb1 i) ha hap).trans hbudget
  have hsum : (∑ i, ‖x i‖^p) ≤ U^p := by
    calc
      _ ≤ ∑ i, U^p*(b i)^p := by
        apply Finset.sum_le_sum
        intro i _
        rw [Real.norm_eq_abs, ← Real.mul_rpow hU (hb0 i)]
        exact Real.rpow_le_rpow (abs_nonneg _) (hx i) hp.le
      _ = U^p*(∑ i, (b i)^p) := by rw [Finset.mul_sum]
      _ ≤ U^p*1 := mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hU p)
      _ = U^p := mul_one _
  have h := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg (x i)) p)
    hsum (one_div_nonneg.mpr hp.le)
  rw [one_div, Real.rpow_rpow_inv hU hp.ne'] at h
  simpa only [lpNorm, one_div] using h

theorem rows_norm_cap12 {p ell u v w : ℝ} (hp : 12 ≤ p)
    (hell : 0 ≤ ell) (hu : u ≤ 9/10) (hv : 0 ≤ v) (hw : w ≤ 53/50)
    (X : Fin 3 → Fin 3 → ℝ)
    (hbox : ∀ j i, if j = i then -u ≤ X j i ∧ X j i ≤ -ell
      else v ≤ X j i ∧ X j i ≤ w) : ∀ j, lpNorm p (X j) ≤ 23/20 := by
  intro j
  apply norm_cap_of_power_budget (a := (12 : ℝ))
    (b := fun i => if j = i then (18/23 : ℝ) else 106/115)
    (by linarith) (by norm_num) hp (by norm_num)
  · intro i; split_ifs <;> norm_num
  · intro i; split_ifs <;> norm_num
  · intro i
    have h := hbox j i
    by_cases hji : j = i
    · simp only [if_pos hji] at h ⊢
      norm_num
      exact abs_le.mpr ⟨by linarith [h.1],by linarith [h.2]⟩
    · simp only [if_neg hji] at h ⊢
      norm_num
      exact abs_le.mpr ⟨by linarith [h.1],by linarith [h.2]⟩
  · fin_cases j <;> norm_num [Fin.sum_univ_three,Real.rpow_natCast,Fin.ext_iff]

end HlawkaSchatten.DiagonalCutoff12

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalCutoff8
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
open HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff16Scalar

theorem pair_tail_of_box {p ell u v w A rho eps : ℝ} (m : ℕ)
    (hm : 1 ≤ m) (hp : (m : ℝ) ≤ p)
    (hv : 0 ≤ v) (hr : 0 ≤ rho) (hr1 : rho ≤ 1) (heps : 0 ≤ eps)
    (hlo : u-v ≤ rho*(2*v)) (hhi : min (w-ell) (A-v) ≤ rho*(2*v))
    (hcert : 6*rho^m ≤ (m : ℝ)*eps)
    (X : Fin 3 → Fin 3 → ℝ)
    (hS : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2) ≤ 3)
    (hT : lpNorm p (X 0+X 1+X 2) ≤ A)
    (hbox : ∀ j i, if j = i then -u ≤ X j i ∧ X j i ≤ -ell
      else v ≤ X j i ∧ X j i ≤ w) :
    ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      lpNorm p (X j+X k) ≤ X j i+X k i+eps := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hp1 : 1 ≤ p := hm1.trans hp
  intro i j k hij hik hjk
  have hji := hbox j i
  have hki := hbox k i
  have hjj := hbox j j
  have hkk := hbox k k
  have hjk' := hbox j k
  have hkj := hbox k j
  simp only [if_neg hij.symm] at hji
  simp only [if_neg hik.symm] at hki
  simp only [if_pos rfl] at hjj hkk
  simp only [if_neg hjk] at hjk'
  simp only [if_neg hjk.symm] at hkj
  have hmain : 2*v ≤ X j i+X k i := by linarith only [hji.1,hki.1]
  have hm0 : 0 ≤ X j i+X k i := by linarith only [hmain,hv]
  have hscaled := mul_le_mul_of_nonneg_left hmain hr
  have hcol (l : Fin 3) : X i l+X j l+X k l ≤ A := by
    have h := (norm_apply_le_lpNorm hp1 (X 0+X 1+X 2) l).trans hT
    have hs := sum3 (fun r => X r l) hij hik hjk
    simp only [Fin.sum_univ_three,Real.norm_eq_abs,Pi.add_apply] at h hs
    linarith only [h,hs,le_abs_self (X 0 l+X 1 l+X 2 l)]
  have hij' := hbox i j
  have hik' := hbox i k
  simp only [if_neg hij] at hij'
  simp only [if_neg hik] at hik'
  have hjup : X j j+X k j ≤ min (w-ell) (A-v) := by
    exact le_min (by linarith only [hjj.2,hkj.2]) (by linarith only [hcol j,hij'.1])
  have hkup : X j k+X k k ≤ min (w-ell) (A-v) := by
    exact le_min (by linarith only [hjk'.2,hkk.2]) (by linarith only [hcol k,hik'.1])
  have hsum := sum3 (fun l => lpNorm p (X l)) hij hik hjk
  rw [Fin.sum_univ_three] at hsum
  have hni := lpNorm_nonneg p (X i)
  have hnj := norm_apply_le_lpNorm hp1 (X j) i
  have hnk := norm_apply_le_lpNorm hp1 (X k) i
  rw [Real.norm_eq_abs] at hnj hnk
  have hcap : X j i+X k i ≤ 3 := by
    linarith only [hS,hsum,hni,hnj,hnk,le_abs_self (X j i),le_abs_self (X k i)]
  rw [lpNorm_eq3 p _ hij hik hjk]
  simp only [Pi.add_apply]
  apply two_tail_norm_bound (cap := (3 : ℝ)) m hm hp hm0 hcap
    (by norm_num) hr hr1 heps
  · exact abs_le.mpr ⟨by linarith only [hjj.1,hkj.1,hlo,hscaled],
      by linarith only [hjup,hhi,hscaled]⟩
  · exact abs_le.mpr ⟨by linarith only [hjk'.1,hkk.1,hlo,hscaled],
      by linarith only [hkup,hhi,hscaled]⟩
  · nlinarith only [hcert]

theorem rows_norm_cap {p ell u v w U : ℝ} (m : ℕ)
    (hm : 1 ≤ m) (hp : (m : ℝ) ≤ p)
    (hell : 0 ≤ ell) (hu0 : 0 ≤ u) (hv : 0 ≤ v) (hw0 : 0 ≤ w)
    (hU : 0 < U) (hu : u ≤ U) (hw : w ≤ U)
    (hbudget : (u/U)^m+2*(w/U)^m ≤ 1)
    (X : Fin 3 → Fin 3 → ℝ)
    (hbox : ∀ j i, if j = i then -u ≤ X j i ∧ X j i ≤ -ell
      else v ≤ X j i ∧ X j i ≤ w) : ∀ j, lpNorm p (X j) ≤ U := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  intro j
  apply HlawkaSchatten.DiagonalCutoff12.norm_cap_of_power_budget (a := (m : ℝ))
    (b := fun i => if j = i then u/U else w/U)
    (by linarith) (by positivity) hp hU.le
  · intro i; split_ifs <;> positivity
  · intro i; split_ifs
    · exact (div_le_one hU).mpr hu
    · exact (div_le_one hU).mpr hw
  · intro i
    have h := hbox j i
    by_cases hji : j = i
    · simp only [if_pos hji] at h ⊢
      have he : U*(u/U) = u := by field_simp
      rw [he]
      exact abs_le.mpr ⟨h.1,by linarith [h.2]⟩
    · simp only [if_neg hji] at h ⊢
      have he : U*(w/U) = w := by field_simp
      rw [he]
      exact abs_le.mpr ⟨by linarith [h.1],h.2⟩
  · fin_cases j <;> norm_num [Fin.sum_univ_three,Real.rpow_natCast,Fin.ext_iff] <;>
      nlinarith only [hbudget]

end HlawkaSchatten.DiagonalCutoff8

set_option autoImplicit false
namespace HlawkaSchatten.DiagonalCutoff8
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem coupled_relation_of_failure {p k eps : ℝ} (hp : 1 ≤ p)
    (hk : 0 < k) (hK : k ≤ cyclicConstant p) (X : Fin 3 → Fin 3 → ℝ)
    (hS : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2) = 3)
    (tails : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      lpNorm p (X j+X k) ≤ X j i+X k i+eps)
    (hf : tripleDeficit p (cyclicConstant p) X < 0) :
    lpNorm p (X 0+X 1+X 2) ≤ k*(X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1)+3-6*k+3*k*(eps) := by
  have t0 := tails 0 1 2 (by decide) (by decide) (by decide)
  have t1 := tails 1 0 2 (by decide) (by decide) (by decide)
  have t2 := tails 2 0 1 (by decide) (by decide) (by decide)
  have hP : lpNorm p (X 1+X 2)+lpNorm p (X 0+X 2)+lpNorm p (X 0+X 1) ≤
      X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1+3*(eps) := by linarith
  have hG := pairGapSum_nonneg hp (X 0) (X 1) (X 2)
  have hkg := mul_le_mul_of_nonneg_right hK hG
  change hlawkaDeficit p (cyclicConstant p) (X 0) (X 1) (X 2) < 0 at hf
  rw [HlawkaSchatten.DiagonalConstruction.hlawkaDeficit_eq,tripleGap,hS] at hf
  have hP' := mul_le_mul_of_nonneg_left hP hk.le
  have hlin : k*pairGapSum (lpNorm p) (X 0) (X 1) (X 2)+lpNorm p (X 0+X 1+X 2) < 3 := by
    linarith only [hkg,hf]
  dsimp only [pairGapSum,pairGap] at hlin
  have hS' := congrArg (fun r : ℝ => k*r) hS
  nlinarith only [hlin,hS',hP']

theorem offsum_floor_from_total {T W k eps : ℝ} (hk : 0 < k) (hT : 1 ≤ T)
    (hC : T ≤ k*W+3-6*k+3*k*(eps)) : 6-2/k-3*(eps) ≤ W := by
  have hbound : (6-W-3*(eps))*k ≤ 2 := by nlinarith
  have h := (le_div_iff₀ hk).mpr hbound
  linarith

end HlawkaSchatten.DiagonalCutoff8

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace HlawkaSchatten.DiagonalCutoff8
open HlawkaSchatten.DiagonalCutoff12
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle
open scoped BigOperators

theorem support_w010_s0_0 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-321061/100000000 : ℝ)*x 0 + (13519973/25000000 : ℝ)*x 1 + (54079891/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-321061/100000000 : ℝ), (13519973/25000000 : ℝ), (54079891/100000000 : ℝ)] ![(1521392321/1000000000000 : ℝ), (499239301927/1000000000000 : ℝ), (99847858299/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s0_1 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (25207303/50000000 : ℝ)*x 0 + (-5740971/100000000 : ℝ)*x 1 + (54079891/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(25207303/50000000 : ℝ), (-5740971/100000000 : ℝ), (54079891/100000000 : ℝ)] ![(450364933/976562500 : ℝ), (39586996571/1000000000000 : ℝ), (99847858299/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s0_2 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (25207303/50000000 : ℝ)*x 0 + (5407989/10000000 : ℝ)*x 1 + (-2870487/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(25207303/50000000 : ℝ), (5407989/10000000 : ℝ), (-2870487/50000000 : ℝ)] ![(450364933/976562500 : ℝ), (249619640531/500000000000 : ℝ), (9896754987/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s0_3 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (50906159/100000000 : ℝ)*x 0 + (1553489/5000000 : ℝ)*x 1 + (31069807/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(50906159/100000000 : ℝ), (1553489/5000000 : ℝ), (31069807/100000000 : ℝ)] ![(466258360979/1000000000000 : ℝ), (133435341751/500000000000 : ℝ), (266870945583/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s0_4 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-8058367/50000000 : ℝ)*x 0 + (12003813/25000000 : ℝ)*x 1 + (3000953/6250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-8058367/50000000 : ℝ), (12003813/25000000 : ℝ), (3000953/6250000 : ℝ)] ![(127103820277/1000000000000 : ℝ), (436448098813/1000000000000 : ℝ), (17457922309/40000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s0_5 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (54568873/100000000 : ℝ)*x 0 + (-8197689/100000000 : ℝ)*x 1 + (48015253/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(54568873/100000000 : ℝ), (-8197689/100000000 : ℝ), (48015253/100000000 : ℝ)] ![(126085880191/250000000000 : ℝ), (59208356677/1000000000000 : ℝ), (218224054543/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s0_6 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (27284437/50000000 : ℝ)*x 0 + (24007629/50000000 : ℝ)*x 1 + (-8197681/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(27284437/50000000 : ℝ), (24007629/50000000 : ℝ), (-8197681/100000000 : ℝ)] ![(63042941401/125000000000 : ℝ), (436448160447/1000000000000 : ℝ), (2960414569/50000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s0_7 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (10134143/100000000 : ℝ)*x 0 + (5053119/10000000 : ℝ)*x 1 + (50531207/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(10134143/100000000 : ℝ), (5053119/10000000 : ℝ), (50531207/100000000 : ℝ)] ![(4702605299/62500000000 : ℝ), (462379066059/1000000000000 : ℝ), (9247584837/20000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s0_8 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-12377929/100000000 : ℝ)*x 0 + (8323321/20000000 : ℝ)*x 1 + (11486693/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-12377929/100000000 : ℝ), (8323321/20000000 : ℝ), (11486693/20000000 : ℝ)] ![(47161592503/500000000000 : ℝ), (371313174651/1000000000000 : ℝ), (534363629081/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s0_9 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (12153153/25000000 : ℝ)*x 0 + (-444629/12500000 : ℝ)*x 1 + (57433491/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(12153153/25000000 : ℝ), (-444629/12500000 : ℝ), (57433491/100000000 : ℝ)] ![(442589242217/1000000000000 : ℝ), (23046839899/1000000000000 : ℝ), (534363902453/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s0_10 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (48612587/100000000 : ℝ)*x 0 + (7179189/12500000 : ℝ)*x 1 + (-3557037/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(48612587/100000000 : ℝ), (7179189/12500000 : ℝ), (-3557037/100000000 : ℝ)] ![(221294492499/500000000000 : ℝ), (267182061627/500000000000 : ℝ), (23046876509/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s0_11 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (70321729/100000000 : ℝ)*x 0 + (5052091/25000000 : ℝ)*x 1 + (10104151/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(70321729/100000000 : ℝ), (5052091/25000000 : ℝ), (10104151/50000000 : ℝ)] ![(671736193081/1000000000000 : ℝ), (82066091419/500000000000 : ℝ), (164131613771/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s0_12 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1714667/100000000 : ℝ)*x 0 + (14797429/25000000 : ℝ)*x 1 + (24035971/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-1714667/100000000 : ℝ), (14797429/25000000 : ℝ), (24035971/50000000 : ℝ)] ![(10103680389/1000000000000 : ℝ), (276432917429/500000000000 : ℝ), (437030474019/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s0_13 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (54531471/100000000 : ℝ)*x 0 + (-1634839/20000000 : ℝ)*x 1 + (48071941/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(54531471/100000000 : ℝ), (-1634839/20000000 : ℝ), (48071941/100000000 : ℝ)] ![(503952889849/1000000000000 : ℝ), (29508316181/500000000000 : ℝ), (87406092749/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s0_14 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (13632867/25000000 : ℝ)*x 0 + (6008993/12500000 : ℝ)*x 1 + (-4087097/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(13632867/25000000 : ℝ), (6008993/12500000 : ℝ), (-4087097/50000000 : ℝ)] ![(251976429259/500000000000 : ℝ), (218515247283/500000000000 : ℝ), (59016624203/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s0_15 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1056311/10000000 : ℝ)*x 0 + (25178327/50000000 : ℝ)*x 1 + (10071331/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(1056311/10000000 : ℝ), (25178327/50000000 : ℝ), (10071331/20000000 : ℝ)] ![(78850666779/1000000000000 : ℝ), (460574654207/1000000000000 : ℝ), (460574664543/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem base_bounds_w010_s0 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (X : Fin 3 → Fin 3 → ℝ)
    (hS : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2) ≤ 3)
    (hT : lpNorm p (X 0+X 1+X 2) ≤ (139773/100000 : ℝ))
    (hC : lpNorm p (X 0+X 1+X 2) ≤ (346501/100000 : ℝ)*(X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1)+(-354761697/20000000 : ℝ)) :
    -(1691/2000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(999/2000 : ℝ) ∧ (3863/5000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (10853/10000 : ℝ) := by

  have hn0 := lpNorm_nonneg p (X 0)

  have hn1 := lpNorm_nonneg p (X 1)

  have hn2 := lpNorm_nonneg p (X 2)

  have hu0 : lpNorm p (X 0) ≤ 3 := by linarith only [hS,hn0,hn1,hn2]

  have hl0 : -3 ≤ lpNorm p (X 0) := by linarith only [hn0]

  have hb00 : -3 ≤ X 0 0 ∧ X 0 0 ≤ 3 := by
    have h := (norm_apply_le_lpNorm (by linarith : (1 : ℝ) ≤ p) (X 0) 0).trans hu0
    simpa only [Real.norm_eq_abs,abs_le] using h

  have hb01 : -3 ≤ X 0 1 ∧ X 0 1 ≤ 3 := by
    have h := (norm_apply_le_lpNorm (by linarith : (1 : ℝ) ≤ p) (X 0) 1).trans hu0
    simpa only [Real.norm_eq_abs,abs_le] using h

  have hb02 : -3 ≤ X 0 2 ∧ X 0 2 ≤ 3 := by
    have h := (norm_apply_le_lpNorm (by linarith : (1 : ℝ) ≤ p) (X 0) 2).trans hu0
    simpa only [Real.norm_eq_abs,abs_le] using h

  have hu1 : lpNorm p (X 1) ≤ 3 := by linarith only [hS,hn0,hn1,hn2]

  have hl1 : -3 ≤ lpNorm p (X 1) := by linarith only [hn1]

  have hb10 : -3 ≤ X 1 0 ∧ X 1 0 ≤ 3 := by
    have h := (norm_apply_le_lpNorm (by linarith : (1 : ℝ) ≤ p) (X 1) 0).trans hu1
    simpa only [Real.norm_eq_abs,abs_le] using h

  have hb11 : -3 ≤ X 1 1 ∧ X 1 1 ≤ 3 := by
    have h := (norm_apply_le_lpNorm (by linarith : (1 : ℝ) ≤ p) (X 1) 1).trans hu1
    simpa only [Real.norm_eq_abs,abs_le] using h

  have hb12 : -3 ≤ X 1 2 ∧ X 1 2 ≤ 3 := by
    have h := (norm_apply_le_lpNorm (by linarith : (1 : ℝ) ≤ p) (X 1) 2).trans hu1
    simpa only [Real.norm_eq_abs,abs_le] using h

  have hu2 : lpNorm p (X 2) ≤ 3 := by linarith only [hS,hn0,hn1,hn2]

  have hl2 : -3 ≤ lpNorm p (X 2) := by linarith only [hn2]

  have hb20 : -3 ≤ X 2 0 ∧ X 2 0 ≤ 3 := by
    have h := (norm_apply_le_lpNorm (by linarith : (1 : ℝ) ≤ p) (X 2) 0).trans hu2
    simpa only [Real.norm_eq_abs,abs_le] using h

  have hb21 : -3 ≤ X 2 1 ∧ X 2 1 ≤ 3 := by
    have h := (norm_apply_le_lpNorm (by linarith : (1 : ℝ) ≤ p) (X 2) 1).trans hu2
    simpa only [Real.norm_eq_abs,abs_le] using h

  have hb22 : -3 ≤ X 2 2 ∧ X 2 2 ≤ 3 := by
    have h := (norm_apply_le_lpNorm (by linarith : (1 : ℝ) ≤ p) (X 2) 2).trans hu2
    simpa only [Real.norm_eq_abs,abs_le] using h

  have h25 := support_w010_s0_0 p hpa hpb (X 0)

  have h26 := support_w010_s0_1 p hpa hpb (X 1)

  have h27 := support_w010_s0_2 p hpa hpb (X 2)

  have h28 := (support_w010_s0_3 p hpa hpb (X 0+X 1+X 2)).trans hT
  simp only [Pi.add_apply] at h28

  have h29 := (support_w010_s0_3 p hpa hpb (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h29

  have h30 := support_w010_s0_4 p hpa hpb (X 0)

  have h31 := support_w010_s0_5 p hpa hpb (X 1)

  have h32 := support_w010_s0_6 p hpa hpb (X 2)

  have h34 := (support_w010_s0_7 p hpa hpb (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h34

  have h35 := support_w010_s0_8 p hpa hpb (X 0)

  have h36 := support_w010_s0_9 p hpa hpb (X 1)

  have h37 := support_w010_s0_10 p hpa hpb (X 2)

  have h39 := (support_w010_s0_11 p hpa hpb (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h39

  have h40 := support_w010_s0_12 p hpa hpb (X 0)

  have h41 := support_w010_s0_13 p hpa hpb (X 1)

  have h42 := support_w010_s0_14 p hpa hpb (X 2)

  have h43 := (support_w010_s0_15 p hpa hpb (X 0+X 1+X 2)).trans hT
  simp only [Pi.add_apply] at h43

  have h44 := (support_w010_s0_15 p hpa hpb (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h44

  refine ⟨?_,?_,?_,?_⟩

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hb10.2, hb22.1, hS, h27, h30, h31, h32, h34, h35, h36, h40, h44]

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hu2, hS, h25, h26, h27, h28, h29, h31, h36, h37, h40, h43]

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hb12.2, hS, h25, h26, h28, h29, h32, h35, h36, h37, h39, h40]

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hb22.1, hS, h26, h27, h29, h30, h31, h32, h40, h41, h42, h44]

theorem coupled_box_w010_s0 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (X : Fin 3 → Fin 3 → ℝ)
    (hS : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2) ≤ 3)
    (hT : lpNorm p (X 0+X 1+X 2) ≤ (139773/100000 : ℝ))
    (hC : lpNorm p (X 0+X 1+X 2) ≤ (346501/100000 : ℝ)*(X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1)+(-354761697/20000000 : ℝ)) :
    ∀ j i, if j = i then -(1691/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(999/2000 : ℝ)
      else (3863/5000 : ℝ) ≤ X j i ∧ X j i ≤ (10853/10000 : ℝ) := by
  exact coordinateBox_of_base_bounds (fun Y hS hT hC => base_bounds_w010_s0 p hpa hpb Y hS hT hC)
    X hS hT hC

end HlawkaSchatten.DiagonalCutoff8

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace HlawkaSchatten.DiagonalCutoff8
open HlawkaSchatten.DiagonalCutoff12
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle
open scoped BigOperators

theorem support_w010_s1_0 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1081551/50000000 : ℝ)*x 0 + (53522801/100000000 : ℝ)*x 1 + (53522797/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-1081551/50000000 : ℝ), (53522801/100000000 : ℝ), (53522797/100000000 : ℝ)] ![(2627432967/200000000000 : ℝ), (493431432637/1000000000000 : ℝ), (123357847741/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s1_1 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2042553/4000000 : ℝ)*x 0 + (-112483/2000000 : ℝ)*x 1 + (10704561/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(2042553/4000000 : ℝ), (-112483/2000000 : ℝ), (10704561/20000000 : ℝ)] ![(467890628879/1000000000000 : ℝ), (38677880751/1000000000000 : ℝ), (49343147431/100000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s1_2 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (51063823/100000000 : ℝ)*x 0 + (53522807/100000000 : ℝ)*x 1 + (-112483/2000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(51063823/100000000 : ℝ), (53522807/100000000 : ℝ), (-112483/2000000 : ℝ)] ![(467890608169/1000000000000 : ℝ), (493431495147/1000000000000 : ℝ), (38677880751/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s1_3 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4735337/10000000 : ℝ)*x 0 + (8236997/25000000 : ℝ)*x 1 + (32947987/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(4735337/10000000 : ℝ), (8236997/25000000 : ℝ), (32947987/100000000 : ℝ)] ![(429655240861/1000000000000 : ℝ), (285172376673/1000000000000 : ℝ), (71293091723/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s1_4 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-11675969/100000000 : ℝ)*x 0 + (1559351/3125000 : ℝ)*x 1 + (1559351/3125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-11675969/100000000 : ℝ), (1559351/3125000 : ℝ), (1559351/3125000 : ℝ)] ![(44150455553/500000000000 : ℝ), (227924768597/500000000000 : ℝ), (227924768597/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s1_5 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (13337443/25000000 : ℝ)*x 0 + (-1843211/25000000 : ℝ)*x 1 + (1559351/3125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(13337443/25000000 : ℝ), (-1843211/25000000 : ℝ), (1559351/3125000 : ℝ)] ![(98325828129/200000000000 : ℝ), (6565163579/125000000000 : ℝ), (227924768597/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s1_6 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (13337443/25000000 : ℝ)*x 0 + (1559351/3125000 : ℝ)*x 1 + (-1843211/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(13337443/25000000 : ℝ), (1559351/3125000 : ℝ), (-1843211/25000000 : ℝ)] ![(98325828129/200000000000 : ℝ), (227924768597/500000000000 : ℝ), (6565163579/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s1_7 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (23730281/100000000 : ℝ)*x 0 + (44606343/100000000 : ℝ)*x 1 + (5575793/12500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(23730281/100000000 : ℝ), (44606343/100000000 : ℝ), (5575793/12500000 : ℝ)] ![(307511593/1562500000 : ℝ), (12549883591/31250000000 : ℝ), (200798142543/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s1_8 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-4745583/50000000 : ℝ)*x 0 + (11688317/25000000 : ℝ)*x 1 + (27393547/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-4745583/50000000 : ℝ), (11688317/25000000 : ℝ), (27393547/50000000 : ℝ)] ![(17467388399/250000000000 : ℝ), (423507089577/1000000000000 : ℝ), (506623340481/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s1_9 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5027181/10000000 : ℝ)*x 0 + (-2487939/50000000 : ℝ)*x 1 + (6848387/12500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(5027181/10000000 : ℝ), (-2487939/50000000 : ℝ), (6848387/12500000 : ℝ)] ![(7182778157/15625000000 : ℝ), (33678818093/1000000000000 : ℝ), (506623361381/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s1_10 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (50271811/100000000 : ℝ)*x 0 + (10957419/20000000 : ℝ)*x 1 + (-4975879/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(50271811/100000000 : ℝ), (10957419/20000000 : ℝ), (-4975879/100000000 : ℝ)] ![(229848906191/500000000000 : ℝ), (506623350931/1000000000000 : ℝ), (16839412871/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s1_11 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (55029033/100000000 : ℝ)*x 0 + (28849757/100000000 : ℝ)*x 1 + (14424877/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(55029033/100000000 : ℝ), (28849757/100000000 : ℝ), (14424877/50000000 : ℝ)] ![(127288082543/250000000000 : ℝ), (122711920663/500000000000 : ℝ), (49084762497/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s1_12 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3623237/100000000 : ℝ)*x 0 + (28186393/50000000 : ℝ)*x 1 + (49646673/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-3623237/100000000 : ℝ), (28186393/50000000 : ℝ), (49646673/100000000 : ℝ)] ![(23532180591/1000000000000 : ℝ), (261612384663/500000000000 : ℝ), (113310760403/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s1_13 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (53511147/100000000 : ℝ)*x 0 + (-7487709/100000000 : ℝ)*x 1 + (3102917/6250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(53511147/100000000 : ℝ), (-7487709/100000000 : ℝ), (3102917/6250000 : ℝ)] ![(246655009631/500000000000 : ℝ), (26723467561/500000000000 : ℝ), (90648606259/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s1_14 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6688893/12500000 : ℝ)*x 0 + (49646671/100000000 : ℝ)*x 1 + (-3743857/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(6688893/12500000 : ℝ), (49646671/100000000 : ℝ), (-3743857/50000000 : ℝ)] ![(61663748501/125000000000 : ℝ), (226621510489/500000000000 : ℝ), (10689395091/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s1_15 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (21973719/100000000 : ℝ)*x 0 + (5676311/12500000 : ℝ)*x 1 + (22705237/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(21973719/100000000 : ℝ), (5676311/12500000 : ℝ), (22705237/50000000 : ℝ)] ![(180425337487/1000000000000 : ℝ), (204893698487/500000000000 : ℝ), (409787254203/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem base_bounds_w010_s1 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (X : Fin 3 → Fin 3 → ℝ)
    (hS : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2) ≤ 3)
    (hT : lpNorm p (X 0+X 1+X 2) ≤ (139773/100000 : ℝ))
    (hC : lpNorm p (X 0+X 1+X 2) ≤ (346501/100000 : ℝ)*(X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1)+(-17786733371064867/1000000000000000 : ℝ)) :
    -(7751/10000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(3053/5000 : ℝ) ∧ (1687/2000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (4993/5000 : ℝ) := by

  have hn0 := lpNorm_nonneg p (X 0)

  have hn1 := lpNorm_nonneg p (X 1)

  have hn2 := lpNorm_nonneg p (X 2)

  have hu0 : lpNorm p (X 0) ≤ 3 := by linarith only [hS,hn0,hn1,hn2]

  have hl0 : -3 ≤ lpNorm p (X 0) := by linarith only [hn0]

  have hb00 : -3 ≤ X 0 0 ∧ X 0 0 ≤ 3 := by
    have h := (norm_apply_le_lpNorm (by linarith : (1 : ℝ) ≤ p) (X 0) 0).trans hu0
    simpa only [Real.norm_eq_abs,abs_le] using h

  have hb01 : -3 ≤ X 0 1 ∧ X 0 1 ≤ 3 := by
    have h := (norm_apply_le_lpNorm (by linarith : (1 : ℝ) ≤ p) (X 0) 1).trans hu0
    simpa only [Real.norm_eq_abs,abs_le] using h

  have hb02 : -3 ≤ X 0 2 ∧ X 0 2 ≤ 3 := by
    have h := (norm_apply_le_lpNorm (by linarith : (1 : ℝ) ≤ p) (X 0) 2).trans hu0
    simpa only [Real.norm_eq_abs,abs_le] using h

  have hu1 : lpNorm p (X 1) ≤ 3 := by linarith only [hS,hn0,hn1,hn2]

  have hl1 : -3 ≤ lpNorm p (X 1) := by linarith only [hn1]

  have hb10 : -3 ≤ X 1 0 ∧ X 1 0 ≤ 3 := by
    have h := (norm_apply_le_lpNorm (by linarith : (1 : ℝ) ≤ p) (X 1) 0).trans hu1
    simpa only [Real.norm_eq_abs,abs_le] using h

  have hb11 : -3 ≤ X 1 1 ∧ X 1 1 ≤ 3 := by
    have h := (norm_apply_le_lpNorm (by linarith : (1 : ℝ) ≤ p) (X 1) 1).trans hu1
    simpa only [Real.norm_eq_abs,abs_le] using h

  have hb12 : -3 ≤ X 1 2 ∧ X 1 2 ≤ 3 := by
    have h := (norm_apply_le_lpNorm (by linarith : (1 : ℝ) ≤ p) (X 1) 2).trans hu1
    simpa only [Real.norm_eq_abs,abs_le] using h

  have hu2 : lpNorm p (X 2) ≤ 3 := by linarith only [hS,hn0,hn1,hn2]

  have hl2 : -3 ≤ lpNorm p (X 2) := by linarith only [hn2]

  have hb20 : -3 ≤ X 2 0 ∧ X 2 0 ≤ 3 := by
    have h := (norm_apply_le_lpNorm (by linarith : (1 : ℝ) ≤ p) (X 2) 0).trans hu2
    simpa only [Real.norm_eq_abs,abs_le] using h

  have hb21 : -3 ≤ X 2 1 ∧ X 2 1 ≤ 3 := by
    have h := (norm_apply_le_lpNorm (by linarith : (1 : ℝ) ≤ p) (X 2) 1).trans hu2
    simpa only [Real.norm_eq_abs,abs_le] using h

  have hb22 : -3 ≤ X 2 2 ∧ X 2 2 ≤ 3 := by
    have h := (norm_apply_le_lpNorm (by linarith : (1 : ℝ) ≤ p) (X 2) 2).trans hu2
    simpa only [Real.norm_eq_abs,abs_le] using h

  have h25 := support_w010_s1_0 p hpa hpb (X 0)

  have h26 := support_w010_s1_1 p hpa hpb (X 1)

  have h27 := support_w010_s1_2 p hpa hpb (X 2)

  have h28 := (support_w010_s1_3 p hpa hpb (X 0+X 1+X 2)).trans hT
  simp only [Pi.add_apply] at h28

  have h29 := (support_w010_s1_3 p hpa hpb (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h29

  have h30 := support_w010_s1_4 p hpa hpb (X 0)

  have h31 := support_w010_s1_5 p hpa hpb (X 1)

  have h32 := support_w010_s1_6 p hpa hpb (X 2)

  have h33 := (support_w010_s1_7 p hpa hpb (X 0+X 1+X 2)).trans hT
  simp only [Pi.add_apply] at h33

  have h34 := (support_w010_s1_7 p hpa hpb (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h34

  have h35 := support_w010_s1_8 p hpa hpb (X 0)

  have h36 := support_w010_s1_9 p hpa hpb (X 1)

  have h37 := support_w010_s1_10 p hpa hpb (X 2)

  have h39 := (support_w010_s1_11 p hpa hpb (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h39

  have h40 := support_w010_s1_12 p hpa hpb (X 0)

  have h41 := support_w010_s1_13 p hpa hpb (X 1)

  have h42 := support_w010_s1_14 p hpa hpb (X 2)

  have h44 := (support_w010_s1_15 p hpa hpb (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h44

  refine ⟨?_,?_,?_,?_⟩

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hb22.1, hS, h27, h30, h31, h32, h34, h39, h40, h41, h44]

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hb20.2, hS, h25, h26, h27, h28, h29, h31, h33, h35, h37, h42]

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hb11.1, hb12.2, hb22.1, hS, h25, h26, h27, h35, h36, h37, h39, h44]

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hb11.1, hb20.2, hS, h30, h31, h33, h34, h35, h40, h41, h42, h44]

theorem coupled_box_w010_s1 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (X : Fin 3 → Fin 3 → ℝ)
    (hS : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2) ≤ 3)
    (hT : lpNorm p (X 0+X 1+X 2) ≤ (139773/100000 : ℝ))
    (hC : lpNorm p (X 0+X 1+X 2) ≤ (346501/100000 : ℝ)*(X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1)+(-17786733371064867/1000000000000000 : ℝ)) :
    ∀ j i, if j = i then -(7751/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(3053/5000 : ℝ)
      else (1687/2000 : ℝ) ≤ X j i ∧ X j i ≤ (4993/5000 : ℝ) := by
  exact coordinateBox_of_base_bounds (fun Y hS hT hC => base_bounds_w010_s1 p hpa hpb Y hS hT hC)
    X hS hT hC

end HlawkaSchatten.DiagonalCutoff8

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace HlawkaSchatten.DiagonalCutoff8
open HlawkaSchatten.DiagonalCutoff12
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle
open scoped BigOperators

theorem support_w010_s2_0 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2488283/100000000 : ℝ)*x 0 + (13353667/25000000 : ℝ)*x 1 + (53414671/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-2488283/100000000 : ℝ), (13353667/25000000 : ℝ), (53414671/100000000 : ℝ)] ![(7694959397/500000000000 : ℝ), (492305016627/1000000000000 : ℝ), (246152523937/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s2_1 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (51131593/100000000 : ℝ)*x 0 + (-1419683/25000000 : ℝ)*x 1 + (53414689/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(51131593/100000000 : ℝ), (-1419683/25000000 : ℝ), (53414689/100000000 : ℝ)] ![(468592411861/1000000000000 : ℝ), (39102342137/1000000000000 : ℝ), (246152617677/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s2_2 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (51131597/100000000 : ℝ)*x 0 + (53414683/100000000 : ℝ)*x 1 + (-2839367/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(51131597/100000000 : ℝ), (53414683/100000000 : ℝ), (-2839367/50000000 : ℝ)] ![(468592453287/1000000000000 : ℝ), (492305172861/1000000000000 : ℝ), (391023577/10000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s2_3 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (46684773/100000000 : ℝ)*x 0 + (3329787/10000000 : ℝ)*x 1 + (8324469/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(46684773/100000000 : ℝ), (3329787/10000000 : ℝ), (8324469/25000000 : ℝ)] ![(422805996193/1000000000000 : ℝ), (57719393647/200000000000 : ℝ), (144298513501/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s2_4 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-11146521/100000000 : ℝ)*x 0 + (50117661/100000000 : ℝ)*x 1 + (25058833/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-11146521/100000000 : ℝ), (50117661/100000000 : ℝ), (25058833/50000000 : ℝ)] ![(16757914871/200000000000 : ℝ), (458105184097/1000000000000 : ℝ), (91621047149/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s2_5 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (53210543/100000000 : ℝ)*x 0 + (-7272631/100000000 : ℝ)*x 1 + (25058833/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(53210543/100000000 : ℝ), (-7272631/100000000 : ℝ), (25058833/50000000 : ℝ)] ![(490179465599/1000000000000 : ℝ), (51715283439/1000000000000 : ℝ), (91621047149/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s2_6 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (13302637/25000000 : ℝ)*x 0 + (50117661/100000000 : ℝ)*x 1 + (-909079/12500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(13302637/25000000 : ℝ), (50117661/100000000 : ℝ), (-909079/12500000 : ℝ)] ![(490179517651/1000000000000 : ℝ), (458105184097/1000000000000 : ℝ), (2068611659/40000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s2_7 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (25235741/100000000 : ℝ)*x 0 + (43909417/100000000 : ℝ)*x 1 + (2744339/6250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(25235741/100000000 : ℝ), (43909417/100000000 : ℝ), (2744339/6250000 : ℝ)] ![(105487144733/500000000000 : ℝ), (394512808391/1000000000000 : ℝ), (78902575893/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s2_8 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-9176883/100000000 : ℝ)*x 0 + (47297227/100000000 : ℝ)*x 1 + (13625849/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-9176883/100000000 : ℝ), (47297227/100000000 : ℝ), (13625849/25000000 : ℝ)] ![(1050948083/15625000000 : ℝ), (214539807019/500000000000 : ℝ), (251829847061/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s2_9 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (12612369/25000000 : ℝ)*x 0 + (-5122973/100000000 : ℝ)*x 1 + (272517/500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(12612369/25000000 : ℝ), (-5122973/100000000 : ℝ), (272517/500000 : ℝ)] ![(9230683563/20000000000 : ℝ), (6961214473/200000000000 : ℝ), (251829867947/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s2_10 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (50449473/100000000 : ℝ)*x 0 + (54503403/100000000 : ℝ)*x 1 + (-1280743/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(50449473/100000000 : ℝ), (54503403/100000000 : ℝ), (-1280743/25000000 : ℝ)] ![(92306829427/200000000000 : ℝ), (503659767223/1000000000000 : ℝ), (2175379043/62500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s2_11 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (53328763/100000000 : ℝ)*x 0 + (29770613/100000000 : ℝ)*x 1 + (232583/781250 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(53328763/100000000 : ℝ), (29770613/100000000 : ℝ), (232583/781250 : ℝ)] ![(491410359951/1000000000000 : ℝ), (254294757401/1000000000000 : ℝ), (7946714487/31250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s2_12 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1934261/50000000 : ℝ)*x 0 + (55996533/100000000 : ℝ)*x 1 + (1246343/2500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-1934261/50000000 : ℝ), (55996533/100000000 : ℝ), (1246343/2500000 : ℝ)] ![(12670130873/500000000000 : ℝ), (259640009503/500000000000 : ℝ), (113844927677/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s2_13 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (53378821/100000000 : ℝ)*x 0 + (-184841/2500000 : ℝ)*x 1 + (24926853/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(53378821/100000000 : ℝ), (-184841/2500000 : ℝ), (24926853/50000000 : ℝ)] ![(122982916417/250000000000 : ℝ), (52688752633/1000000000000 : ℝ), (455379566193/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s2_14 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (13344711/25000000 : ℝ)*x 0 + (49853707/100000000 : ℝ)*x 1 + (-7393609/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(13344711/25000000 : ℝ), (49853707/100000000 : ℝ), (-7393609/100000000 : ℝ)] ![(98386381041/200000000000 : ℝ), (113844894129/250000000000 : ℝ), (6586062873/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w010_s2_15 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (x : Fin 3 → ℝ) :
    (23414991/100000000 : ℝ)*x 0 + (11187851/25000000 : ℝ)*x 1 + (44751409/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (139/16 : ℝ)) 139 123 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(23414991/100000000 : ℝ), (11187851/25000000 : ℝ), (44751409/100000000 : ℝ)] ![(24231872037/125000000000 : ℝ), (50384059353/125000000000 : ℝ), (403072525717/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem base_bounds_w010_s2 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (X : Fin 3 → Fin 3 → ℝ)
    (hS : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2) ≤ 3)
    (hT : lpNorm p (X 0+X 1+X 2) ≤ (139773/100000 : ℝ))
    (hC : lpNorm p (X 0+X 1+X 2) ≤ (346501/100000 : ℝ)*(X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1)+(-8894999479152417/500000000000000 : ℝ)) :
    -(7677/10000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(1551/2500 : ℝ) ∧ (8509/10000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (4951/5000 : ℝ) := by

  have hn0 := lpNorm_nonneg p (X 0)

  have hn1 := lpNorm_nonneg p (X 1)

  have hn2 := lpNorm_nonneg p (X 2)

  have hu0 : lpNorm p (X 0) ≤ 3 := by linarith only [hS,hn0,hn1,hn2]

  have hl0 : -3 ≤ lpNorm p (X 0) := by linarith only [hn0]

  have hb00 : -3 ≤ X 0 0 ∧ X 0 0 ≤ 3 := by
    have h := (norm_apply_le_lpNorm (by linarith : (1 : ℝ) ≤ p) (X 0) 0).trans hu0
    simpa only [Real.norm_eq_abs,abs_le] using h

  have hb01 : -3 ≤ X 0 1 ∧ X 0 1 ≤ 3 := by
    have h := (norm_apply_le_lpNorm (by linarith : (1 : ℝ) ≤ p) (X 0) 1).trans hu0
    simpa only [Real.norm_eq_abs,abs_le] using h

  have hb02 : -3 ≤ X 0 2 ∧ X 0 2 ≤ 3 := by
    have h := (norm_apply_le_lpNorm (by linarith : (1 : ℝ) ≤ p) (X 0) 2).trans hu0
    simpa only [Real.norm_eq_abs,abs_le] using h

  have hu1 : lpNorm p (X 1) ≤ 3 := by linarith only [hS,hn0,hn1,hn2]

  have hl1 : -3 ≤ lpNorm p (X 1) := by linarith only [hn1]

  have hb10 : -3 ≤ X 1 0 ∧ X 1 0 ≤ 3 := by
    have h := (norm_apply_le_lpNorm (by linarith : (1 : ℝ) ≤ p) (X 1) 0).trans hu1
    simpa only [Real.norm_eq_abs,abs_le] using h

  have hb11 : -3 ≤ X 1 1 ∧ X 1 1 ≤ 3 := by
    have h := (norm_apply_le_lpNorm (by linarith : (1 : ℝ) ≤ p) (X 1) 1).trans hu1
    simpa only [Real.norm_eq_abs,abs_le] using h

  have hb12 : -3 ≤ X 1 2 ∧ X 1 2 ≤ 3 := by
    have h := (norm_apply_le_lpNorm (by linarith : (1 : ℝ) ≤ p) (X 1) 2).trans hu1
    simpa only [Real.norm_eq_abs,abs_le] using h

  have hu2 : lpNorm p (X 2) ≤ 3 := by linarith only [hS,hn0,hn1,hn2]

  have hl2 : -3 ≤ lpNorm p (X 2) := by linarith only [hn2]

  have hb20 : -3 ≤ X 2 0 ∧ X 2 0 ≤ 3 := by
    have h := (norm_apply_le_lpNorm (by linarith : (1 : ℝ) ≤ p) (X 2) 0).trans hu2
    simpa only [Real.norm_eq_abs,abs_le] using h

  have hb21 : -3 ≤ X 2 1 ∧ X 2 1 ≤ 3 := by
    have h := (norm_apply_le_lpNorm (by linarith : (1 : ℝ) ≤ p) (X 2) 1).trans hu2
    simpa only [Real.norm_eq_abs,abs_le] using h

  have hb22 : -3 ≤ X 2 2 ∧ X 2 2 ≤ 3 := by
    have h := (norm_apply_le_lpNorm (by linarith : (1 : ℝ) ≤ p) (X 2) 2).trans hu2
    simpa only [Real.norm_eq_abs,abs_le] using h

  have h25 := support_w010_s2_0 p hpa hpb (X 0)

  have h26 := support_w010_s2_1 p hpa hpb (X 1)

  have h27 := support_w010_s2_2 p hpa hpb (X 2)

  have h28 := (support_w010_s2_3 p hpa hpb (X 0+X 1+X 2)).trans hT
  simp only [Pi.add_apply] at h28

  have h29 := (support_w010_s2_3 p hpa hpb (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h29

  have h30 := support_w010_s2_4 p hpa hpb (X 0)

  have h31 := support_w010_s2_5 p hpa hpb (X 1)

  have h32 := support_w010_s2_6 p hpa hpb (X 2)

  have h34 := (support_w010_s2_7 p hpa hpb (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h34

  have h35 := support_w010_s2_8 p hpa hpb (X 0)

  have h36 := support_w010_s2_9 p hpa hpb (X 1)

  have h37 := support_w010_s2_10 p hpa hpb (X 2)

  have h39 := (support_w010_s2_11 p hpa hpb (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h39

  have h40 := support_w010_s2_12 p hpa hpb (X 0)

  have h41 := support_w010_s2_13 p hpa hpb (X 1)

  have h42 := support_w010_s2_14 p hpa hpb (X 2)

  have h43 := (support_w010_s2_15 p hpa hpb (X 0+X 1+X 2)).trans hT
  simp only [Pi.add_apply] at h43

  have h44 := (support_w010_s2_15 p hpa hpb (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h44

  refine ⟨?_,?_,?_,?_⟩

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hb10.2, hb22.1, hS, h26, h27, h29, h30, h31, h32, h34, h40, h41]

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hb20.2, hS, h25, h26, h27, h28, h29, h31, h32, h36, h39, h40]

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hb21.2, hb22.1, hS, h27, h28, h29, h30, h35, h36, h37, h39, h41]

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hb10.2, hb22.1, hS, h25, h32, h35, h36, h40, h41, h42, h43, h44]

theorem coupled_box_w010_s2 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) (X : Fin 3 → Fin 3 → ℝ)
    (hS : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2) ≤ 3)
    (hT : lpNorm p (X 0+X 1+X 2) ≤ (139773/100000 : ℝ))
    (hC : lpNorm p (X 0+X 1+X 2) ≤ (346501/100000 : ℝ)*(X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1)+(-8894999479152417/500000000000000 : ℝ)) :
    ∀ j i, if j = i then -(7677/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(1551/2500 : ℝ)
      else (8509/10000 : ℝ) ≤ X j i ∧ X j i ≤ (4951/5000 : ℝ) := by
  exact coordinateBox_of_base_bounds (fun Y hS hT hC => base_bounds_w010_s2 p hpa hpb Y hS hT hC)
    X hS hT hC

end HlawkaSchatten.DiagonalCutoff8

/- Finite scalar certificates transported by Bernoulli.
Every rational power comparison is proved exactly by Lean. -/
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten.DiagonalCutoff16Scalar
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 20000
namespace HlawkaSchatten.DiagonalCutoff8

theorem lower_w010_000 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (1105/128 : ℝ)) :
    (346501/862500 : ℝ)*p < cyclicConstant p := by

  have ht : (759426043/1000000000 : ℝ) ^ (69/8 : ℝ) ≤ (23287739169/250000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (759426043/1000000000 : ℝ)) (X := (23287739169/250000000000 : ℝ)) (by norm_num) (by norm_num) 69 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have hA : (523287739169/250000000000 : ℝ) ≤ (1089417297783/1000000000000 : ℝ) ^ (69/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1089417297783/1000000000000 : ℝ)) (X := (523287739169/250000000000 : ℝ)) (by norm_num) 69 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have ha : (3 : ℝ) ≤ (283960815679/250000000000 : ℝ) ^ (69/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (283960815679/250000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 69 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  apply HlawkaSchatten.DiagonalCutoff8Scalar.cyclicConstant_lower_endpoint (alpha := (69/8 : ℝ)) (beta := (1105/128 : ℝ))
    (t := (759426043/1000000000 : ℝ)) (Aup := (1089417297783/1000000000000 : ℝ)) (aup := (283960815679/250000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower_w010_001 (p : ℝ) (hpa : (1105/128 : ℝ) ≤ p) (hpb : p ≤ (553/64 : ℝ)) :
    (346501/862500 : ℝ)*p < cyclicConstant p := by

  have ht : (759426043/1000000000 : ℝ) ^ (1105/128 : ℝ) ≤ (3718036113/40000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (759426043/1000000000 : ℝ)) (X := (3718036113/40000000000 : ℝ)) (by norm_num) (by norm_num) 1105 128 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have hA : (83718036113/40000000000 : ℝ) ≤ (544660402557/500000000000 : ℝ) ^ (1105/128 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (544660402557/500000000000 : ℝ)) (X := (83718036113/40000000000 : ℝ)) (by norm_num) 1105 128 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have ha : (3 : ℝ) ≤ (567856169783/500000000000 : ℝ) ^ (1105/128 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (567856169783/500000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 1105 128 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  apply HlawkaSchatten.DiagonalCutoff8Scalar.cyclicConstant_lower_endpoint (alpha := (1105/128 : ℝ)) (beta := (553/64 : ℝ))
    (t := (759426043/1000000000 : ℝ)) (Aup := (544660402557/500000000000 : ℝ)) (aup := (567856169783/500000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower_w010_002 (p : ℝ) (hpa : (553/64 : ℝ) ≤ p) (hpb : p ≤ (277/32 : ℝ)) :
    (346501/862500 : ℝ)*p < cyclicConstant p := by

  have ht : (759426043/1000000000 : ℝ) ^ (553/64 : ℝ) ≤ (18550255723/200000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (759426043/1000000000 : ℝ)) (X := (18550255723/200000000000 : ℝ)) (by norm_num) (by norm_num) 553 64 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have hA : (418550255723/200000000000 : ℝ) ≤ (217844904037/200000000000 : ℝ) ^ (553/64 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (217844904037/200000000000 : ℝ)) (X := (418550255723/200000000000 : ℝ)) (by norm_num) 553 64 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have ha : (3 : ℝ) ≤ (1135581668217/1000000000000 : ℝ) ^ (553/64 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1135581668217/1000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 553 64 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  apply HlawkaSchatten.DiagonalCutoff8Scalar.cyclicConstant_lower_endpoint (alpha := (553/64 : ℝ)) (beta := (277/32 : ℝ))
    (t := (759426043/1000000000 : ℝ)) (Aup := (217844904037/200000000000 : ℝ)) (aup := (1135581668217/1000000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower_w010_003 (p : ℝ) (hpa : (277/32 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) :
    (346501/862500 : ℝ)*p < cyclicConstant p := by

  have ht : (759426043/1000000000 : ℝ) ^ (277/32 : ℝ) ≤ (11544164429/125000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (759426043/1000000000 : ℝ)) (X := (11544164429/125000000000 : ℝ)) (by norm_num) (by norm_num) 277 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have hA : (261544164429/125000000000 : ℝ) ≤ (1089032570987/1000000000000 : ℝ) ^ (277/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1089032570987/1000000000000 : ℝ)) (X := (261544164429/125000000000 : ℝ)) (by norm_num) 277 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have ha : (3 : ℝ) ≤ (1135321078023/1000000000000 : ℝ) ^ (277/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1135321078023/1000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 277 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  apply HlawkaSchatten.DiagonalCutoff8Scalar.cyclicConstant_lower_endpoint (alpha := (277/32 : ℝ)) (beta := (139/16 : ℝ))
    (t := (759426043/1000000000 : ℝ)) (Aup := (1089032570987/1000000000000 : ℝ)) (aup := (1135321078023/1000000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem scalar_lower_w010 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) :
    (346501/862500 : ℝ)*p < cyclicConstant p := by

  by_cases h0 : p ≤ (1105/128 : ℝ)
  · exact lower_w010_000 p (by linarith) h0

  by_cases h1 : p ≤ (553/64 : ℝ)
  · exact lower_w010_001 p (by linarith) h1

  by_cases h2 : p ≤ (277/32 : ℝ)
  · exact lower_w010_002 p (by linarith) h2

  exact lower_w010_003 p (by linarith) hpb

theorem envelope_w010 (p : ℝ) (hp : (69/8 : ℝ) ≤ p) :
    scalarEnvelope p (46591/100000 : ℝ) < (346501/862500 : ℝ)*p := by

  have hq : (46591/100000 : ℝ) ^ (69/8 : ℝ) ≤ (1377542563/1000000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (46591/100000 : ℝ)) (X := (1377542563/1000000000000 : ℝ)) (by norm_num) (by norm_num) 69 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have hb : (500707931259/1000000000000 : ℝ) ≤ (639593/693002 : ℝ) ^ (69/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (639593/693002 : ℝ)) (X := (500707931259/1000000000000 : ℝ)) (by norm_num) 69 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  apply envelope_linear_of_certificate (69/8 : ℝ) (by norm_num) hp
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he : (1-((1-(46591/100000 : ℝ))/(2*(346501/862500 : ℝ)))/(69/8 : ℝ) : ℝ) = (639593/693002 : ℝ) := by norm_num
  rw [he]
  linarith only [hq, hb]

end HlawkaSchatten.DiagonalCutoff8

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace HlawkaSchatten.DiagonalCutoff8
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
open HlawkaSchatten.DiagonalCutoff8Scalar
theorem curvature_w010 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) :
    p * (310884299972494346471/31919275993102922160 : ℝ) * (258440277/794825690 : ℝ) ^ (p-2) < 1 ∧
    (7385294293486701851720293025/462210785037997262897434992 : ℝ) * (5038525/13197459 : ℝ) ^ (p-2) < 2*(346501/868750 : ℝ)-1/p := by
  have hp0 : 0 < p := by linarith

  have hrT : (258440277/794825690 : ℝ) ^ (p-2) ≤ (258440277/794825690 : ℝ) ^ (6 : ℕ) := by
    have h := Real.rpow_le_rpow_of_exponent_ge' (x := (258440277/794825690 : ℝ))
      (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) ≤ 6) (by linarith : (6 : ℝ) ≤ p-2)
    calc _ ≤ (258440277/794825690 : ℝ) ^ ((6 : ℕ) : ℝ) := h
         _ = _ := Real.rpow_natCast _ _

  have hrC : (5038525/13197459 : ℝ) ^ (p-2) ≤ (5038525/13197459 : ℝ) ^ (6 : ℕ) := by
    have h := Real.rpow_le_rpow_of_exponent_ge' (x := (5038525/13197459 : ℝ))
      (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) ≤ 6) (by linarith : (6 : ℝ) ≤ p-2)
    calc _ ≤ (5038525/13197459 : ℝ) ^ ((6 : ℕ) : ℝ) := h
         _ = _ := Real.rpow_natCast _ _

  constructor
  · have h1 := mul_le_mul_of_nonneg_left hrT (show 0 ≤ p*(310884299972494346471/31919275993102922160 : ℝ) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hpb (show 0 ≤ (310884299972494346471/31919275993102922160 : ℝ)*((258440277/794825690 : ℝ) ^ (6 : ℕ)) by norm_num)
    have hend : (139/16 : ℝ)*(310884299972494346471/31919275993102922160 : ℝ)*((258440277/794825690 : ℝ) ^ (6 : ℕ)) < 1 := by norm_num
    nlinarith only [h1,h2,hend]
  · have h1 := mul_le_mul_of_nonneg_left hrC (show 0 ≤ (7385294293486701851720293025/462210785037997262897434992 : ℝ) by norm_num)
    have hinv : 1/p ≤ 1/(69/8 : ℝ) := one_div_le_one_div_of_le (by norm_num) hpa
    have hend : (7385294293486701851720293025/462210785037997262897434992 : ℝ)*((5038525/13197459 : ℝ) ^ (6 : ℕ)) < 2*(346501/868750 : ℝ)-1/(69/8 : ℝ) := by norm_num
    linarith only [h1,hinv,hend]

theorem localized_nonnegative_w010 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hS : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2) = 3)
    (hT1 : 1 ≤ lpNorm p (X 0+X 1+X 2)) (hT : lpNorm p (X 0+X 1+X 2) ≤ (139773/100000 : ℝ))
    (hC : lpNorm p (X 0+X 1+X 2) ≤ (346501/100000 : ℝ)*(X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1)+(-8894999479152417/500000000000000 : ℝ)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  have hKlo := scalar_lower_w010 p hpa hpb
  have hKhi := cyclicConstant_upper8 (by linarith : 8 ≤ p) (by linarith : p ≤ 12)
  have hbox := coupled_box_w010_s2 p hpa hpb X hS.le hT hC
  have hrows := rows_norm_cap 8 (by norm_num) (by linarith : (8 : ℝ) ≤ p)
    (by norm_num : (0 : ℝ) ≤ (1551/2500 : ℝ)) (by norm_num : (0 : ℝ) ≤ (7677/10000 : ℝ))
    (by norm_num : (0 : ℝ) ≤ (8509/10000 : ℝ)) (by norm_num : (0 : ℝ) ≤ (4951/5000 : ℝ))
    (by norm_num : (0 : ℝ) < (109/100 : ℝ)) (by norm_num) (by norm_num) (by norm_num) X hbox
  have hoff : (9394999479152417/1732505000000000 : ℝ) ≤ (X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1) := by
    have h := offsum_floor_from_total (k := (346501/100000 : ℝ)) (eps := (29361/5000000000 : ℝ))
      (W := (X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1)) (by norm_num) hT1
      (by norm_num at hC ⊢; linarith only [hC])
    norm_num at h
    exact h
  have hpairs : ∀ i j l : Fin 3, i ≠ j → i ≠ l → j ≠ l →
      (8509/5000 : ℝ) ≤ X j i+X l i := by
    intro i j l hij hil hjl
    have hj := hbox j i
    have hl := hbox l i
    simp only [if_neg hij.symm] at hj
    simp only [if_neg hil.symm] at hl
    linarith only [hj.1,hl.1]
  obtain ⟨hNT,hNC⟩ := curvature_w010 p hpa hpb
  apply HlawkaSchatten.DiagonalCutoff8.nonnegative_of_curvature_margins
    (c := (346501/868750 : ℝ)) (ell := (1551/2500 : ℝ)) (u := (7677/10000 : ℝ)) (v := (8509/10000 : ℝ)) (w := (4951/5000 : ℝ)) (U := (109/100 : ℝ)) (A := (139773/100000 : ℝ)) (J := (8509/5000 : ℝ)) (W0 := (9394999479152417/1732505000000000 : ℝ)) (m := (1551/2500 : ℝ)) (M := (4951/5000 : ℝ)) (L := (8509/5000 : ℝ)) (s := (9341/10000 : ℝ)) (t := (34/25 : ℝ)) (eta := (1849/5000 : ℝ)) (eps1 := (2 : ℝ)) (eps2 := (1/2 : ℝ)) (gT := (6672625613798681/281342778174018 : ℝ)) (gC := (2710199740729064899713869/54320223885062552931888 : ℝ))
    (by linarith) (by linarith) (by nlinarith) hKhi
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num at hNT ⊢; nlinarith only [hNT])
    (by norm_num at hNC ⊢; linarith only [hNC])
    X hbox hrows hT hpairs hoff

theorem real_three_w010 (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  intro x y z
  by_contra hf
  have hneg : hlawkaDeficit p (cyclicConstant p) x y z < 0 := by
    rw [HlawkaSchatten.DiagonalConstruction.hlawkaDeficit_eq]
    exact sub_neg.mpr (lt_of_not_ge hf)
  have hlower := scalar_lower_w010 p hpa hpb
  have hK : (346501/100000 : ℝ) ≤ cyclicConstant p := by nlinarith
  have henv := (envelope_w010 p hpa).trans hlower
  obtain ⟨X,hS,hT1,hT,htails0,hfX⟩ := coarse_failure_reduction
    (by linarith : 8 ≤ p) (by norm_num : (0 : ℝ) < (46591/100000 : ℝ))
    (by norm_num) (by linarith) henv x y z hneg
  norm_num at hT
  have hC0 : lpNorm p (X 0+X 1+X 2) ≤ (346501/100000 : ℝ)*(X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1)+(-354761697/20000000 : ℝ) := by
    have h := coupled_relation_of_failure (eps := (1/200 : ℝ))
      (by linarith : (1 : ℝ) ≤ p) (by norm_num : (0 : ℝ) < (346501/100000 : ℝ)) hK X hS htails0 hfX
    norm_num at h ⊢
    linarith only [h]
  have hbox0 := coupled_box_w010_s0 p hpa hpb X hS.le hT hC0
  have htails1 := pair_tail_of_box (rho := (2929/7726 : ℝ)) (eps := (3200211/10000000000 : ℝ))
    8 (by norm_num) (by linarith : (8 : ℝ) ≤ p)
    (by norm_num : (0 : ℝ) ≤ (3863/5000 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) X hS.le hT hbox0
  have hC1 : lpNorm p (X 0+X 1+X 2) ≤ (346501/100000 : ℝ)*(X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1)+(-17786733371064867/1000000000000000 : ℝ) := by
    have h := coupled_relation_of_failure (eps := (3200211/10000000000 : ℝ))
      (by linarith : (1 : ℝ) ≤ p) (by norm_num : (0 : ℝ) < (346501/100000 : ℝ)) hK X hS htails1 hfX
    norm_num at h ⊢
    linarith only [h]
  have hbox1 := coupled_box_w010_s1 p hpa hpb X hS.le hT hC1
  have htails2 := pair_tail_of_box (rho := (388/1687 : ℝ)) (eps := (29361/5000000000 : ℝ))
    8 (by norm_num) (by linarith : (8 : ℝ) ≤ p)
    (by norm_num : (0 : ℝ) ≤ (1687/2000 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) X hS.le hT hbox1
  have hC2 : lpNorm p (X 0+X 1+X 2) ≤ (346501/100000 : ℝ)*(X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1)+(-8894999479152417/500000000000000 : ℝ) := by
    have h := coupled_relation_of_failure (eps := (29361/5000000000 : ℝ))
      (by linarith : (1 : ℝ) ≤ p) (by norm_num : (0 : ℝ) < (346501/100000 : ℝ)) hK X hS htails2 hfX
    norm_num at h ⊢
    linarith only [h]
  exact (not_lt_of_ge (localized_nonnegative_w010 p hpa hpb X hS hT1 hT hC2)) hfX

end HlawkaSchatten.DiagonalCutoff8


theorem solution (p : ℝ) (hpa : (69/8 : ℝ) ≤ p) (hpb : p ≤ (139/16 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  exact HlawkaSchatten.DiagonalCutoff8.real_three_w010 p hpa hpb

#print axioms solution
