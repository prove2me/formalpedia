-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff8.real_three_w008
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T15:33:01.58468+00:00
-- url     : https://prove2.me/submissions/36102b23-3f50-47dd-99b2-ba774a605205

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

theorem support_w008_s0_0 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-174117/50000000 : ℝ)*x 0 + (10827403/20000000 : ℝ)*x 1 + (54137019/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-174117/50000000 : ℝ), (10827403/20000000 : ℝ), (54137019/100000000 : ℝ)] ![(1647514869/1000000000000 : ℝ), (499176214989/1000000000000 : ℝ), (499176256749/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s0_1 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5055213/10000000 : ℝ)*x 0 + (-5684439/100000000 : ℝ)*x 1 + (27068509/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(5055213/10000000 : ℝ), (-5684439/100000000 : ℝ), (27068509/50000000 : ℝ)] ![(461917601681/1000000000000 : ℝ), (38906145223/1000000000000 : ℝ), (499176246309/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s0_2 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (12638033/25000000 : ℝ)*x 0 + (54137017/100000000 : ℝ)*x 1 + (-1421109/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(12638033/25000000 : ℝ), (54137017/100000000 : ℝ), (-1421109/25000000 : ℝ)] ![(461917622373/1000000000000 : ℝ), (499176235869/1000000000000 : ℝ), (1556244879/40000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s0_3 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2543361/5000000 : ℝ)*x 0 + (7798617/25000000 : ℝ)*x 1 + (7798613/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(2543361/5000000 : ℝ), (7798617/25000000 : ℝ), (7798613/25000000 : ℝ)] ![(116294693003/250000000000 : ℝ), (66852670481/250000000000 : ℝ), (267410526629/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s0_4 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-16343669/100000000 : ℝ)*x 0 + (24004057/50000000 : ℝ)*x 1 + (1200203/2500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-16343669/100000000 : ℝ), (24004057/50000000 : ℝ), (1200203/2500000 : ℝ)] ![(32156566701/250000000000 : ℝ), (108921707647/250000000000 : ℝ), (435686892239/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s0_5 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (54620769/100000000 : ℝ)*x 0 + (-8344159/100000000 : ℝ)*x 1 + (76813/160000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(54620769/100000000 : ℝ), (-8344159/100000000 : ℝ), (76813/160000 : ℝ)] ![(504229516197/1000000000000 : ℝ), (60083534543/1000000000000 : ℝ), (3403804247/7812500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s0_6 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (54620767/100000000 : ℝ)*x 0 + (48008117/100000000 : ℝ)*x 1 + (-834417/10000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(54620767/100000000 : ℝ), (48008117/100000000 : ℝ), (-834417/10000000 : ℝ)] ![(504229495293/1000000000000 : ℝ), (217843430707/500000000000 : ℝ), (1877613257/31250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s0_7 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2618629/25000000 : ℝ)*x 0 + (10095339/20000000 : ℝ)*x 1 + (5047667/10000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(2618629/25000000 : ℝ), (10095339/20000000 : ℝ), (5047667/10000000 : ℝ)] ![(38862873261/500000000000 : ℝ), (461137250169/1000000000000 : ℝ), (230568495789/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s0_8 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-6277791/50000000 : ℝ)*x 0 + (8316173/20000000 : ℝ)*x 1 + (57489703/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-6277791/50000000 : ℝ), (8316173/20000000 : ℝ), (57489703/100000000 : ℝ)] ![(47713885441/500000000000 : ℝ), (370253586721/1000000000000 : ℝ), (66789829463/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s0_9 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (24306567/50000000 : ℝ)*x 0 + (-3679009/100000000 : ℝ)*x 1 + (57489709/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(24306567/50000000 : ℝ), (-3679009/100000000 : ℝ), (57489709/100000000 : ℝ)] ![(13809648767/31250000000 : ℝ), (2377253117/100000000000 : ℝ), (267159349421/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s0_10 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (48613133/100000000 : ℝ)*x 0 + (28744853/50000000 : ℝ)*x 1 + (-1839507/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(48613133/100000000 : ℝ), (28744853/50000000 : ℝ), (-1839507/50000000 : ℝ)] ![(110477187563/250000000000 : ℝ), (534318667273/1000000000000 : ℝ), (95090271/4000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s0_11 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (69972391/100000000 : ℝ)*x 0 + (20503157/100000000 : ℝ)*x 1 + (20503179/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(69972391/100000000 : ℝ), (20503157/100000000 : ℝ), (20503179/100000000 : ℝ)] ![(667453716813/1000000000000 : ℝ), (166273035919/1000000000000 : ℝ), (83136618961/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s0_12 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-358789/20000000 : ℝ)*x 0 + (59285717/100000000 : ℝ)*x 1 + (2402909/5000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-358789/20000000 : ℝ), (59285717/100000000 : ℝ), (2402909/5000000 : ℝ)] ![(5270815999/500000000000 : ℝ), (138314259151/250000000000 : ℝ), (436201309779/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s0_13 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (10917539/20000000 : ℝ)*x 0 + (-1040433/12500000 : ℝ)*x 1 + (2402909/5000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(10917539/20000000 : ℝ), (-1040433/12500000 : ℝ), (2402909/5000000 : ℝ)] ![(15746369863/31250000000 : ℝ), (14978709881/250000000000 : ℝ), (436201309779/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s0_14 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (54587699/100000000 : ℝ)*x 0 + (2402909/5000000 : ℝ)*x 1 + (-416173/5000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(54587699/100000000 : ℝ), (2402909/5000000 : ℝ), (-416173/5000000 : ℝ)] ![(503883877421/1000000000000 : ℝ), (436201309779/1000000000000 : ℝ), (14978701731/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s0_15 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (10846533/100000000 : ℝ)*x 0 + (25162607/50000000 : ℝ)*x 1 + (1572663/3125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(10846533/100000000 : ℝ), (25162607/50000000 : ℝ), (1572663/3125000 : ℝ)] ![(2526830611/31250000000 : ℝ), (9191413849/20000000000 : ℝ), (45957071313/100000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem base_bounds_w008_s0 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (X : Fin 3 → Fin 3 → ℝ)
    (hS : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2) ≤ 3)
    (hT : lpNorm p (X 0+X 1+X 2) ≤ (70089/50000 : ℝ))
    (hC : lpNorm p (X 0+X 1+X 2) ≤ (170447/50000 : ℝ)*(X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1)+(-174025059/10000000 : ℝ)) :
    -(1687/2000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(4977/10000 : ℝ) ∧ (7707/10000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (2711/2500 : ℝ) := by

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

  have h25 := support_w008_s0_0 p hpa hpb (X 0)

  have h26 := support_w008_s0_1 p hpa hpb (X 1)

  have h27 := support_w008_s0_2 p hpa hpb (X 2)

  have h28 := (support_w008_s0_3 p hpa hpb (X 0+X 1+X 2)).trans hT
  simp only [Pi.add_apply] at h28

  have h29 := (support_w008_s0_3 p hpa hpb (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h29

  have h30 := support_w008_s0_4 p hpa hpb (X 0)

  have h31 := support_w008_s0_5 p hpa hpb (X 1)

  have h32 := support_w008_s0_6 p hpa hpb (X 2)

  have h34 := (support_w008_s0_7 p hpa hpb (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h34

  have h35 := support_w008_s0_8 p hpa hpb (X 0)

  have h36 := support_w008_s0_9 p hpa hpb (X 1)

  have h37 := support_w008_s0_10 p hpa hpb (X 2)

  have h39 := (support_w008_s0_11 p hpa hpb (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h39

  have h40 := support_w008_s0_12 p hpa hpb (X 0)

  have h41 := support_w008_s0_13 p hpa hpb (X 1)

  have h42 := support_w008_s0_14 p hpa hpb (X 2)

  have h43 := (support_w008_s0_15 p hpa hpb (X 0+X 1+X 2)).trans hT
  simp only [Pi.add_apply] at h43

  have h44 := (support_w008_s0_15 p hpa hpb (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h44

  refine ⟨?_,?_,?_,?_⟩

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hb11.1, hb20.2, hS, h30, h31, h32, h34, h35, h37, h40, h41, h44]

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hu1, hS, h25, h26, h27, h28, h29, h32, h36, h40, h41, h43]

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hu2, hS, h25, h27, h28, h29, h31, h35, h36, h37, h39]

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hb10.2, hb22.1, hS, h25, h27, h31, h34, h36, h40, h41, h42, h44]

theorem coupled_box_w008_s0 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (X : Fin 3 → Fin 3 → ℝ)
    (hS : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2) ≤ 3)
    (hT : lpNorm p (X 0+X 1+X 2) ≤ (70089/50000 : ℝ))
    (hC : lpNorm p (X 0+X 1+X 2) ≤ (170447/50000 : ℝ)*(X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1)+(-174025059/10000000 : ℝ)) :
    ∀ j i, if j = i then -(1687/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(4977/10000 : ℝ)
      else (7707/10000 : ℝ) ≤ X j i ∧ X j i ≤ (2711/2500 : ℝ) := by
  exact coordinateBox_of_base_bounds (fun Y hS hT hC => base_bounds_w008_s0 p hpa hpb Y hS hT hC)
    X hS hT hC

end HlawkaSchatten.DiagonalCutoff8

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace HlawkaSchatten.DiagonalCutoff8
open HlawkaSchatten.DiagonalCutoff12
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle
open scoped BigOperators

theorem support_w008_s1_0 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1104491/50000000 : ℝ)*x 0 + (53576511/100000000 : ℝ)*x 1 + (53576513/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-1104491/50000000 : ℝ), (53576511/100000000 : ℝ), (53576513/100000000 : ℝ)] ![(13342658859/1000000000000 : ℝ), (493328647963/1000000000000 : ℝ), (246664334407/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s1_1 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (25535433/50000000 : ℝ)*x 0 + (-574599/10000000 : ℝ)*x 1 + (53576507/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(25535433/50000000 : ℝ), (-574599/10000000 : ℝ), (53576507/100000000 : ℝ)] ![(233643961747/500000000000 : ℝ), (7876693287/200000000000 : ℝ), (493328606261/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s1_2 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (51070867/100000000 : ℝ)*x 0 + (26788253/50000000 : ℝ)*x 1 + (-5745989/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(51070867/100000000 : ℝ), (26788253/50000000 : ℝ), (-5745989/100000000 : ℝ)] ![(233643966927/500000000000 : ℝ), (123332148959/250000000000 : ℝ), (1575338347/40000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s1_3 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1481803/3125000 : ℝ)*x 0 + (3301907/10000000 : ℝ)*x 1 + (3301907/10000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(1481803/3125000 : ℝ), (3301907/10000000 : ℝ), (3301907/10000000 : ℝ)] ![(21481252623/50000000000 : ℝ), (71296866647/250000000000 : ℝ), (71296866647/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s1_4 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-5955713/50000000 : ℝ)*x 0 + (779493/1562500 : ℝ)*x 1 + (24943787/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-5955713/50000000 : ℝ), (779493/1562500 : ℝ), (24943787/50000000 : ℝ)] ![(89903613227/1000000000000 : ℝ), (455048070191/1000000000000 : ℝ), (455048297399/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s1_5 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (53402547/100000000 : ℝ)*x 0 + (-1504671/20000000 : ℝ)*x 1 + (49887557/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(53402547/100000000 : ℝ), (-1504671/20000000 : ℝ), (49887557/100000000 : ℝ)] ![(491515375117/1000000000000 : ℝ), (53436484199/1000000000000 : ℝ), (455048121829/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s1_6 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (53402551/100000000 : ℝ)*x 0 + (24943777/50000000 : ℝ)*x 1 + (-3761677/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(53402551/100000000 : ℝ), (24943777/50000000 : ℝ), (-3761677/50000000 : ℝ)] ![(491515416801/1000000000000 : ℝ), (227524045423/500000000000 : ℝ), (26718238079/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s1_7 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5950239/25000000 : ℝ)*x 0 + (44672121/100000000 : ℝ)*x 1 + (44672133/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(5950239/25000000 : ℝ), (44672121/100000000 : ℝ), (44672133/100000000 : ℝ)] ![(196861415419/1000000000000 : ℝ), (401569220243/1000000000000 : ℝ), (200784671189/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s1_8 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-9683113/100000000 : ℝ)*x 0 + (46689011/100000000 : ℝ)*x 1 + (10972023/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-9683113/100000000 : ℝ), (46689011/100000000 : ℝ), (10972023/20000000 : ℝ)] ![(14222119863/200000000000 : ℝ), (84431491613/200000000000 : ℝ), (126682980113/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s1_9 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (50265149/100000000 : ℝ)*x 0 + (-5088141/100000000 : ℝ)*x 1 + (27430061/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(50265149/100000000 : ℝ), (-5088141/100000000 : ℝ), (27430061/50000000 : ℝ)] ![(458949696041/1000000000000 : ℝ), (34318289643/1000000000000 : ℝ), (506731993659/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s1_10 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (50265151/100000000 : ℝ)*x 0 + (13715029/25000000 : ℝ)*x 1 + (-2544073/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(50265151/100000000 : ℝ), (13715029/25000000 : ℝ), (-2544073/50000000 : ℝ)] ![(458949716717/1000000000000 : ℝ), (50673193091/100000000000 : ℝ), (17159163913/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s1_11 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (55062727/100000000 : ℝ)*x 0 + (5786719/20000000 : ℝ)*x 1 + (14466799/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(55062727/100000000 : ℝ), (5786719/20000000 : ℝ), (14466799/50000000 : ℝ)] ![(508851393167/1000000000000 : ℝ), (122787140307/500000000000 : ℝ), (245574309443/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s1_12 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-370501/10000000 : ℝ)*x 0 + (56472621/100000000 : ℝ)*x 1 + (6203989/12500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-370501/10000000 : ℝ), (56472621/100000000 : ℝ), (6203989/12500000 : ℝ)] ![(5990711463/250000000000 : ℝ), (523628320503/1000000000000 : ℝ), (226204406519/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s1_13 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (53566207/100000000 : ℝ)*x 0 + (-477457/6250000 : ℝ)*x 1 + (49631911/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(53566207/100000000 : ℝ), (-477457/6250000 : ℝ), (49631911/100000000 : ℝ)] ![(19728848997/40000000000 : ℝ), (6796243873/125000000000 : ℝ), (452408802717/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s1_14 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (53566213/100000000 : ℝ)*x 0 + (24815957/50000000 : ℝ)*x 1 + (-7639301/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(53566213/100000000 : ℝ), (24815957/50000000 : ℝ), (-7639301/100000000 : ℝ)] ![(123305321869/250000000000 : ℝ), (452408833679/1000000000000 : ℝ), (54369862343/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s1_15 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (22053237/100000000 : ℝ)*x 0 + (45471251/100000000 : ℝ)*x 1 + (2841953/6250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(22053237/100000000 : ℝ), (45471251/100000000 : ℝ), (2841953/6250000 : ℝ)] ![(45143869223/250000000000 : ℝ), (25607016997/62500000000 : ℝ), (204856120673/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem base_bounds_w008_s1 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (X : Fin 3 → Fin 3 → ℝ)
    (hS : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2) ≤ 3)
    (hT : lpNorm p (X 0+X 1+X 2) ≤ (70089/50000 : ℝ))
    (hC : lpNorm p (X 0+X 1+X 2) ≤ (170447/50000 : ℝ)*(X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1)+(-8725130423488413/500000000000000 : ℝ)) :
    -(7739/10000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(759/1250 : ℝ) ∧ (841/1000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (4993/5000 : ℝ) := by

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

  have h25 := support_w008_s1_0 p hpa hpb (X 0)

  have h26 := support_w008_s1_1 p hpa hpb (X 1)

  have h27 := support_w008_s1_2 p hpa hpb (X 2)

  have h29 := (support_w008_s1_3 p hpa hpb (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h29

  have h30 := support_w008_s1_4 p hpa hpb (X 0)

  have h31 := support_w008_s1_5 p hpa hpb (X 1)

  have h32 := support_w008_s1_6 p hpa hpb (X 2)

  have h34 := (support_w008_s1_7 p hpa hpb (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h34

  have h35 := support_w008_s1_8 p hpa hpb (X 0)

  have h36 := support_w008_s1_9 p hpa hpb (X 1)

  have h37 := support_w008_s1_10 p hpa hpb (X 2)

  have h39 := (support_w008_s1_11 p hpa hpb (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h39

  have h40 := support_w008_s1_12 p hpa hpb (X 0)

  have h41 := support_w008_s1_13 p hpa hpb (X 1)

  have h42 := support_w008_s1_14 p hpa hpb (X 2)

  have h43 := (support_w008_s1_15 p hpa hpb (X 0+X 1+X 2)).trans hT
  simp only [Pi.add_apply] at h43

  have h44 := (support_w008_s1_15 p hpa hpb (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h44

  refine ⟨?_,?_,?_,?_⟩

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hb10.2, hb22.1, hS, h26, h27, h30, h31, h32, h34, h39, h40, h44]

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hb22.1, hu1, hS, h25, h26, h27, h29, h36, h37, h39, h40, h44]

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hb11.1, hb21.2, hb22.1, hS, h25, h26, h27, h35, h36, h37, h39, h44]

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hb10.2, hb22.1, hS, h25, h32, h35, h36, h40, h41, h42, h43, h44]

theorem coupled_box_w008_s1 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (X : Fin 3 → Fin 3 → ℝ)
    (hS : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2) ≤ 3)
    (hT : lpNorm p (X 0+X 1+X 2) ≤ (70089/50000 : ℝ))
    (hC : lpNorm p (X 0+X 1+X 2) ≤ (170447/50000 : ℝ)*(X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1)+(-8725130423488413/500000000000000 : ℝ)) :
    ∀ j i, if j = i then -(7739/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(759/1250 : ℝ)
      else (841/1000 : ℝ) ≤ X j i ∧ X j i ≤ (4993/5000 : ℝ) := by
  exact coordinateBox_of_base_bounds (fun Y hS hT hC => base_bounds_w008_s1 p hpa hpb Y hS hT hC)
    X hS hT hC

end HlawkaSchatten.DiagonalCutoff8

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace HlawkaSchatten.DiagonalCutoff8
open HlawkaSchatten.DiagonalCutoff12
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle
open scoped BigOperators

theorem support_w008_s2_0 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2541477/100000000 : ℝ)*x 0 + (26733201/50000000 : ℝ)*x 1 + (26733201/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-2541477/100000000 : ℝ), (26733201/50000000 : ℝ), (26733201/50000000 : ℝ)] ![(15638262149/1000000000000 : ℝ), (492180862097/1000000000000 : ℝ), (492180862097/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s2_1 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2557001/5000000 : ℝ)*x 0 + (-232061/4000000 : ℝ)*x 1 + (26733201/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(2557001/5000000 : ℝ), (-232061/4000000 : ℝ), (26733201/50000000 : ℝ)] ![(468004401233/1000000000000 : ℝ), (248841969/6250000000 : ℝ), (492180862097/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s2_2 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2557001/5000000 : ℝ)*x 0 + (26733201/50000000 : ℝ)*x 1 + (-232061/4000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(2557001/5000000 : ℝ), (26733201/50000000 : ℝ), (-232061/4000000 : ℝ)] ![(468004401233/1000000000000 : ℝ), (492180862097/1000000000000 : ℝ), (248841969/6250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s2_3 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (46749649/100000000 : ℝ)*x 0 + (6673779/20000000 : ℝ)*x 1 + (6673779/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(46749649/100000000 : ℝ), (6673779/20000000 : ℝ), (6673779/20000000 : ℝ)] ![(42277829441/100000000000 : ℝ), (288610844273/1000000000000 : ℝ), (288610844273/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s2_4 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-5686051/50000000 : ℝ)*x 0 + (25054979/50000000 : ℝ)*x 1 + (25054977/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-5686051/50000000 : ℝ), (25054979/50000000 : ℝ), (25054977/50000000 : ℝ)] ![(17061736773/200000000000 : ℝ), (457345671161/1000000000000 : ℝ), (228672814913/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s2_5 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (53260507/100000000 : ℝ)*x 0 + (-7421599/100000000 : ℝ)*x 1 + (12527489/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(53260507/100000000 : ℝ), (-7421599/100000000 : ℝ), (12527489/25000000 : ℝ)] ![(245017716791/500000000000 : ℝ), (10523780381/200000000000 : ℝ), (457345650493/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s2_6 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6657563/12500000 : ℝ)*x 0 + (50109959/100000000 : ℝ)*x 1 + (-7421599/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(6657563/12500000 : ℝ), (50109959/100000000 : ℝ), (-7421599/100000000 : ℝ)] ![(49003540233/100000000000 : ℝ), (228672840747/500000000000 : ℝ), (10523780381/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s2_7 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (25307413/100000000 : ℝ)*x 0 + (43975503/100000000 : ℝ)*x 1 + (21987749/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(25307413/100000000 : ℝ), (43975503/100000000 : ℝ), (21987749/50000000 : ℝ)] ![(211027164953/1000000000000 : ℝ), (394486441033/1000000000000 : ℝ), (394486390249/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s2_8 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-936299/10000000 : ℝ)*x 0 + (47242727/100000000 : ℝ)*x 1 + (54571513/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-936299/10000000 : ℝ), (47242727/100000000 : ℝ), (54571513/100000000 : ℝ)] ![(34227349221/500000000000 : ℝ), (53478821167/125000000000 : ℝ), (503714715779/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s2_9 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (40357/80000 : ℝ)*x 0 + (-523773/10000000 : ℝ)*x 1 + (42634/78125 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(40357/80000 : ℝ), (-523773/10000000 : ℝ), (42634/78125 : ℝ)] ![(460822349817/1000000000000 : ℝ), (17731423597/500000000000 : ℝ), (62964348617/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s2_10 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (10089251/20000000 : ℝ)*x 0 + (54571513/100000000 : ℝ)*x 1 + (-1309433/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(10089251/20000000 : ℝ), (54571513/100000000 : ℝ), (-1309433/25000000 : ℝ)] ![(460822401531/1000000000000 : ℝ), (503714715779/1000000000000 : ℝ), (1418514501/40000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s2_11 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (13341527/25000000 : ℝ)*x 0 + (7463359/25000000 : ℝ)*x 1 + (29853427/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(13341527/25000000 : ℝ), (7463359/25000000 : ℝ), (29853427/100000000 : ℝ)] ![(491135660613/1000000000000 : ℝ), (127216103631/500000000000 : ℝ), (50886424083/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s2_12 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-988817/25000000 : ℝ)*x 0 + (28044919/50000000 : ℝ)*x 1 + (49842707/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-988817/25000000 : ℝ), (28044919/50000000 : ℝ), (49842707/100000000 : ℝ)] ![(516069879/20000000000 : ℝ), (519611541227/1000000000000 : ℝ), (454584955573/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s2_13 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (53431223/100000000 : ℝ)*x 0 + (-1508757/20000000 : ℝ)*x 1 + (49842707/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(53431223/100000000 : ℝ), (-1508757/20000000 : ℝ), (49842707/100000000 : ℝ)] ![(245907109483/500000000000 : ℝ), (53600810769/1000000000000 : ℝ), (454584955573/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s2_14 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (53431223/100000000 : ℝ)*x 0 + (49842707/100000000 : ℝ)*x 1 + (-1508757/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(53431223/100000000 : ℝ), (49842707/100000000 : ℝ), (-1508757/20000000 : ℝ)] ![(245907109483/500000000000 : ℝ), (454584955573/1000000000000 : ℝ), (53600810769/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w008_s2_15 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (x : Fin 3 → ℝ) :
    (183559/781250 : ℝ)*x 0 + (22406241/50000000 : ℝ)*x 1 + (22406241/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (137/16 : ℝ)) 137 121 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(183559/781250 : ℝ), (22406241/50000000 : ℝ), (22406241/50000000 : ℝ)] ![(194003784447/1000000000000 : ℝ), (2014990499/5000000000 : ℝ), (2014990499/5000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem base_bounds_w008_s2 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (X : Fin 3 → Fin 3 → ℝ)
    (hS : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2) ≤ 3)
    (hT : lpNorm p (X 0+X 1+X 2) ≤ (70089/50000 : ℝ))
    (hC : lpNorm p (X 0+X 1+X 2) ≤ (170447/50000 : ℝ)*(X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1)+(-54542418929577/3125000000000 : ℝ)) :
    -(1533/2000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(6171/10000 : ℝ) ∧ (1697/2000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (9901/10000 : ℝ) := by

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

  have h25 := support_w008_s2_0 p hpa hpb (X 0)

  have h26 := support_w008_s2_1 p hpa hpb (X 1)

  have h27 := support_w008_s2_2 p hpa hpb (X 2)

  have h29 := (support_w008_s2_3 p hpa hpb (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h29

  have h30 := support_w008_s2_4 p hpa hpb (X 0)

  have h31 := support_w008_s2_5 p hpa hpb (X 1)

  have h32 := support_w008_s2_6 p hpa hpb (X 2)

  have h34 := (support_w008_s2_7 p hpa hpb (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h34

  have h35 := support_w008_s2_8 p hpa hpb (X 0)

  have h36 := support_w008_s2_9 p hpa hpb (X 1)

  have h37 := support_w008_s2_10 p hpa hpb (X 2)

  have h38 := (support_w008_s2_11 p hpa hpb (X 0+X 1+X 2)).trans hT
  simp only [Pi.add_apply] at h38

  have h39 := (support_w008_s2_11 p hpa hpb (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h39

  have h40 := support_w008_s2_12 p hpa hpb (X 0)

  have h41 := support_w008_s2_13 p hpa hpb (X 1)

  have h42 := support_w008_s2_14 p hpa hpb (X 2)

  have h44 := (support_w008_s2_15 p hpa hpb (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h44

  refine ⟨?_,?_,?_,?_⟩

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hb11.1, hS, h26, h29, h30, h31, h32, h34, h35, h37, h42]

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hS, h25, h26, h27, h29, h39, h44]

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hb12.2, hu1, hS, h25, h26, h29, h35, h36, h37, h38, h39, h42]

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hu2, hS, h30, h32, h34, h36, h40, h41, h42, h44]

theorem coupled_box_w008_s2 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) (X : Fin 3 → Fin 3 → ℝ)
    (hS : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2) ≤ 3)
    (hT : lpNorm p (X 0+X 1+X 2) ≤ (70089/50000 : ℝ))
    (hC : lpNorm p (X 0+X 1+X 2) ≤ (170447/50000 : ℝ)*(X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1)+(-54542418929577/3125000000000 : ℝ)) :
    ∀ j i, if j = i then -(1533/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(6171/10000 : ℝ)
      else (1697/2000 : ℝ) ≤ X j i ∧ X j i ≤ (9901/10000 : ℝ) := by
  exact coordinateBox_of_base_bounds (fun Y hS hT hC => base_bounds_w008_s2 p hpa hpb Y hS hT hC)
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

theorem lower_w008_000 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (1089/128 : ℝ)) :
    (170447/425000 : ℝ)*p < cyclicConstant p := by

  have ht : (758013871/1000000000 : ℝ) ^ (17/2 : ℝ) ≤ (47448862357/500000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (758013871/1000000000 : ℝ)) (X := (47448862357/500000000000 : ℝ)) (by norm_num) (by norm_num) 17 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have hA : (1047448862357/500000000000 : ℝ) ≤ (1090897287213/1000000000000 : ℝ) ^ (17/2 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1090897287213/1000000000000 : ℝ)) (X := (1047448862357/500000000000 : ℝ)) (by norm_num) 17 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have ha : (3 : ℝ) ≤ (1137972880471/1000000000000 : ℝ) ^ (17/2 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1137972880471/1000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 17 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  apply HlawkaSchatten.DiagonalCutoff8Scalar.cyclicConstant_lower_endpoint (alpha := (17/2 : ℝ)) (beta := (1089/128 : ℝ))
    (t := (758013871/1000000000 : ℝ)) (Aup := (1090897287213/1000000000000 : ℝ)) (aup := (1137972880471/1000000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower_w008_001 (p : ℝ) (hpa : (1089/128 : ℝ) ≤ p) (hpb : p ≤ (545/64 : ℝ)) :
    (170447/425000 : ℝ)*p < cyclicConstant p := by

  have ht : (758013871/1000000000 : ℝ) ^ (1089/128 : ℝ) ≤ (94692542509/1000000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (758013871/1000000000 : ℝ)) (X := (94692542509/1000000000000 : ℝ)) (by norm_num) (by norm_num) 1089 128 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have hA : (2094692542509/1000000000000 : ℝ) ≤ (1090797580377/1000000000000 : ℝ) ^ (1089/128 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1090797580377/1000000000000 : ℝ)) (X := (2094692542509/1000000000000 : ℝ)) (by norm_num) 1089 128 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have ha : (3 : ℝ) ≤ (1137837827611/1000000000000 : ℝ) ^ (1089/128 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1137837827611/1000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 1089 128 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  apply HlawkaSchatten.DiagonalCutoff8Scalar.cyclicConstant_lower_endpoint (alpha := (1089/128 : ℝ)) (beta := (545/64 : ℝ))
    (t := (758013871/1000000000 : ℝ)) (Aup := (1090797580377/1000000000000 : ℝ)) (aup := (1137837827611/1000000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower_w008_002 (p : ℝ) (hpa : (545/64 : ℝ) ≤ p) (hpb : p ≤ (273/32 : ℝ)) :
    (170447/425000 : ℝ)*p < cyclicConstant p := by

  have ht : (758013871/1000000000 : ℝ) ^ (545/64 : ℝ) ≤ (94487803937/1000000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (758013871/1000000000 : ℝ)) (X := (94487803937/1000000000000 : ℝ)) (by norm_num) (by norm_num) 545 64 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have hA : (2094487803937/1000000000000 : ℝ) ≤ (545349045739/500000000000 : ℝ) ^ (545/64 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (545349045739/500000000000 : ℝ)) (X := (2094487803937/1000000000000 : ℝ)) (by norm_num) 545 64 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have ha : (3 : ℝ) ≤ (1137703038537/1000000000000 : ℝ) ^ (545/64 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1137703038537/1000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 545 64 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  apply HlawkaSchatten.DiagonalCutoff8Scalar.cyclicConstant_lower_endpoint (alpha := (545/64 : ℝ)) (beta := (273/32 : ℝ))
    (t := (758013871/1000000000 : ℝ)) (Aup := (545349045739/500000000000 : ℝ)) (aup := (1137703038537/1000000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower_w008_003 (p : ℝ) (hpa : (273/32 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) :
    (170447/425000 : ℝ)*p < cyclicConstant p := by

  have ht : (758013871/1000000000 : ℝ) ^ (273/32 : ℝ) ≤ (94079653857/1000000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (758013871/1000000000 : ℝ)) (X := (94079653857/1000000000000 : ℝ)) (by norm_num) (by norm_num) 273 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have hA : (2094079653857/1000000000000 : ℝ) ≤ (545249882379/500000000000 : ℝ) ^ (273/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (545249882379/500000000000 : ℝ)) (X := (2094079653857/1000000000000 : ℝ)) (by norm_num) 273 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have ha : (3 : ℝ) ≤ (1137434248671/1000000000000 : ℝ) ^ (273/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1137434248671/1000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 273 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  apply HlawkaSchatten.DiagonalCutoff8Scalar.cyclicConstant_lower_endpoint (alpha := (273/32 : ℝ)) (beta := (137/16 : ℝ))
    (t := (758013871/1000000000 : ℝ)) (Aup := (545249882379/500000000000 : ℝ)) (aup := (1137434248671/1000000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem scalar_lower_w008 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) :
    (170447/425000 : ℝ)*p < cyclicConstant p := by

  by_cases h0 : p ≤ (1089/128 : ℝ)
  · exact lower_w008_000 p (by linarith) h0

  by_cases h1 : p ≤ (545/64 : ℝ)
  · exact lower_w008_001 p (by linarith) h1

  by_cases h2 : p ≤ (273/32 : ℝ)
  · exact lower_w008_002 p (by linarith) h2

  exact lower_w008_003 p (by linarith) hpb

theorem envelope_w008 (p : ℝ) (hp : (17/2 : ℝ) ≤ p) :
    scalarEnvelope p (23363/50000 : ℝ) < (170447/425000 : ℝ)*p := by

  have hq : (23363/50000 : ℝ) ^ (17/2 : ℝ) ≤ (1553274241/1000000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (23363/50000 : ℝ)) (X := (1553274241/1000000000000 : ℝ)) (by norm_num) (by norm_num) 17 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have hb : (500792279157/1000000000000 : ℝ) ≤ (314257/340894 : ℝ) ^ (17/2 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (314257/340894 : ℝ)) (X := (500792279157/1000000000000 : ℝ)) (by norm_num) 17 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  apply envelope_linear_of_certificate (17/2 : ℝ) (by norm_num) hp
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he : (1-((1-(23363/50000 : ℝ))/(2*(170447/425000 : ℝ)))/(17/2 : ℝ) : ℝ) = (314257/340894 : ℝ) := by norm_num
  rw [he]
  linarith only [hq, hb]

end HlawkaSchatten.DiagonalCutoff8

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace HlawkaSchatten.DiagonalCutoff8
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
open HlawkaSchatten.DiagonalCutoff8Scalar
theorem curvature_w008 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) :
    p * (15340334411335476957/1548089122939515200 : ℝ) * (26143197/78952925 : ℝ) ^ (p-2) < 1 ∧
    (87986926993840683735958425/5439005206632853240888096 : ℝ) * (4065700/10472187 : ℝ) ^ (p-2) < 2*(170447/428125 : ℝ)-1/p := by
  have hp0 : 0 < p := by linarith

  have hrT : (26143197/78952925 : ℝ) ^ (p-2) ≤ (26143197/78952925 : ℝ) ^ (6 : ℕ) := by
    have h := Real.rpow_le_rpow_of_exponent_ge' (x := (26143197/78952925 : ℝ))
      (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) ≤ 6) (by linarith : (6 : ℝ) ≤ p-2)
    calc _ ≤ (26143197/78952925 : ℝ) ^ ((6 : ℕ) : ℝ) := h
         _ = _ := Real.rpow_natCast _ _

  have hrC : (4065700/10472187 : ℝ) ^ (p-2) ≤ (4065700/10472187 : ℝ) ^ (6 : ℕ) := by
    have h := Real.rpow_le_rpow_of_exponent_ge' (x := (4065700/10472187 : ℝ))
      (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) ≤ 6) (by linarith : (6 : ℝ) ≤ p-2)
    calc _ ≤ (4065700/10472187 : ℝ) ^ ((6 : ℕ) : ℝ) := h
         _ = _ := Real.rpow_natCast _ _

  constructor
  · have h1 := mul_le_mul_of_nonneg_left hrT (show 0 ≤ p*(15340334411335476957/1548089122939515200 : ℝ) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hpb (show 0 ≤ (15340334411335476957/1548089122939515200 : ℝ)*((26143197/78952925 : ℝ) ^ (6 : ℕ)) by norm_num)
    have hend : (137/16 : ℝ)*(15340334411335476957/1548089122939515200 : ℝ)*((26143197/78952925 : ℝ) ^ (6 : ℕ)) < 1 := by norm_num
    nlinarith only [h1,h2,hend]
  · have h1 := mul_le_mul_of_nonneg_left hrC (show 0 ≤ (87986926993840683735958425/5439005206632853240888096 : ℝ) by norm_num)
    have hinv : 1/p ≤ 1/(17/2 : ℝ) := one_div_le_one_div_of_le (by norm_num) hpa
    have hend : (87986926993840683735958425/5439005206632853240888096 : ℝ)*((4065700/10472187 : ℝ) ^ (6 : ℕ)) < 2*(170447/428125 : ℝ)-1/(17/2 : ℝ) := by norm_num
    linarith only [h1,hinv,hend]

theorem localized_nonnegative_w008 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hS : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2) = 3)
    (hT1 : 1 ≤ lpNorm p (X 0+X 1+X 2)) (hT : lpNorm p (X 0+X 1+X 2) ≤ (70089/50000 : ℝ))
    (hC : lpNorm p (X 0+X 1+X 2) ≤ (170447/50000 : ℝ)*(X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1)+(-54542418929577/3125000000000 : ℝ)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  have hKlo := scalar_lower_w008 p hpa hpb
  have hKhi := cyclicConstant_upper8 (by linarith : 8 ≤ p) (by linarith : p ≤ 12)
  have hbox := coupled_box_w008_s2 p hpa hpb X hS.le hT hC
  have hrows := rows_norm_cap 8 (by norm_num) (by linarith : (8 : ℝ) ≤ p)
    (by norm_num : (0 : ℝ) ≤ (6171/10000 : ℝ)) (by norm_num : (0 : ℝ) ≤ (1533/2000 : ℝ))
    (by norm_num : (0 : ℝ) ≤ (1697/2000 : ℝ)) (by norm_num : (0 : ℝ) ≤ (9901/10000 : ℝ))
    (by norm_num : (0 : ℝ) < (109/100 : ℝ)) (by norm_num) (by norm_num) (by norm_num) X hbox
  have hoff : (57667418929577/10652937500000 : ℝ) ≤ (X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1) := by
    have h := offsum_floor_from_total (k := (170447/50000 : ℝ)) (eps := (403/62500000 : ℝ))
      (W := (X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1)) (by norm_num) hT1
      (by norm_num at hC ⊢; linarith only [hC])
    norm_num at h
    exact h
  have hpairs : ∀ i j l : Fin 3, i ≠ j → i ≠ l → j ≠ l →
      (1697/1000 : ℝ) ≤ X j i+X l i := by
    intro i j l hij hil hjl
    have hj := hbox j i
    have hl := hbox l i
    simp only [if_neg hij.symm] at hj
    simp only [if_neg hil.symm] at hl
    linarith only [hj.1,hl.1]
  obtain ⟨hNT,hNC⟩ := curvature_w008 p hpa hpb
  apply HlawkaSchatten.DiagonalCutoff8.nonnegative_of_curvature_margins
    (c := (170447/428125 : ℝ)) (ell := (6171/10000 : ℝ)) (u := (1533/2000 : ℝ)) (v := (1697/2000 : ℝ)) (w := (9901/10000 : ℝ)) (U := (109/100 : ℝ)) (A := (70089/50000 : ℝ)) (J := (1697/1000 : ℝ)) (W0 := (57667418929577/10652937500000 : ℝ)) (m := (6171/10000 : ℝ)) (M := (9901/10000 : ℝ)) (L := (1697/1000 : ℝ)) (s := (1861/2000 : ℝ)) (t := (13631/10000 : ℝ)) (eta := (373/1000 : ℝ)) (eps1 := (2 : ℝ)) (eps2 := (1/2 : ℝ)) (gT := (13351030819264993/556472813784976 : ℝ)) (gC := (161443902740992080249465/3205070834786595899168 : ℝ))
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

theorem real_three_w008 (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  intro x y z
  by_contra hf
  have hneg : hlawkaDeficit p (cyclicConstant p) x y z < 0 := by
    rw [HlawkaSchatten.DiagonalConstruction.hlawkaDeficit_eq]
    exact sub_neg.mpr (lt_of_not_ge hf)
  have hlower := scalar_lower_w008 p hpa hpb
  have hK : (170447/50000 : ℝ) ≤ cyclicConstant p := by nlinarith
  have henv := (envelope_w008 p hpa).trans hlower
  obtain ⟨X,hS,hT1,hT,htails0,hfX⟩ := coarse_failure_reduction
    (by linarith : 8 ≤ p) (by norm_num : (0 : ℝ) < (23363/50000 : ℝ))
    (by norm_num) (by linarith) henv x y z hneg
  norm_num at hT
  have hC0 : lpNorm p (X 0+X 1+X 2) ≤ (170447/50000 : ℝ)*(X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1)+(-174025059/10000000 : ℝ) := by
    have h := coupled_relation_of_failure (eps := (1/200 : ℝ))
      (by linarith : (1 : ℝ) ≤ p) (by norm_num : (0 : ℝ) < (170447/50000 : ℝ)) hK X hS htails0 hfX
    norm_num at h ⊢
    linarith only [h]
  have hbox0 := coupled_box_w008_s0 p hpa hpb X hS.le hT hC0
  have htails1 := pair_tail_of_box (rho := (5867/15414 : ℝ)) (eps := (3304207/10000000000 : ℝ))
    8 (by norm_num) (by linarith : (8 : ℝ) ≤ p)
    (by norm_num : (0 : ℝ) ≤ (7707/10000 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) X hS.le hT hbox0
  have hC1 : lpNorm p (X 0+X 1+X 2) ≤ (170447/50000 : ℝ)*(X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1)+(-8725130423488413/500000000000000 : ℝ) := by
    have h := coupled_relation_of_failure (eps := (3304207/10000000000 : ℝ))
      (by linarith : (1 : ℝ) ≤ p) (by norm_num : (0 : ℝ) < (170447/50000 : ℝ)) hK X hS htails1 hfX
    norm_num at h ⊢
    linarith only [h]
  have hbox1 := coupled_box_w008_s1 p hpa hpb X hS.le hT hC1
  have htails2 := pair_tail_of_box (rho := (1957/8410 : ℝ)) (eps := (403/62500000 : ℝ))
    8 (by norm_num) (by linarith : (8 : ℝ) ≤ p)
    (by norm_num : (0 : ℝ) ≤ (841/1000 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) X hS.le hT hbox1
  have hC2 : lpNorm p (X 0+X 1+X 2) ≤ (170447/50000 : ℝ)*(X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1)+(-54542418929577/3125000000000 : ℝ) := by
    have h := coupled_relation_of_failure (eps := (403/62500000 : ℝ))
      (by linarith : (1 : ℝ) ≤ p) (by norm_num : (0 : ℝ) < (170447/50000 : ℝ)) hK X hS htails2 hfX
    norm_num at h ⊢
    linarith only [h]
  exact (not_lt_of_ge (localized_nonnegative_w008 p hpa hpb X hS hT1 hT hC2)) hfX

end HlawkaSchatten.DiagonalCutoff8


theorem solution (p : ℝ) (hpa : (17/2 : ℝ) ≤ p) (hpb : p ≤ (137/16 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  exact HlawkaSchatten.DiagonalCutoff8.real_three_w008 p hpa hpb

#print axioms solution
