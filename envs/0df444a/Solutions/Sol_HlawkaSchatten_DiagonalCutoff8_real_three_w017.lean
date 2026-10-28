-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff8.real_three_w017
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T15:37:33.558871+00:00
-- url     : https://prove2.me/submissions/bdc8852c-119c-4443-a36f-fcab76efae26

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

theorem support_w017_s0_0 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-73153/50000000 : ℝ)*x 0 + (210386/390625 : ℝ)*x 1 + (210386/390625 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-73153/50000000 : ℝ), (210386/390625 : ℝ), (210386/390625 : ℝ)] ![(331609949/500000000000 : ℝ), (99933676347/200000000000 : ℝ), (99933676347/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s0_1 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (49126631/100000000 : ℝ)*x 0 + (-858143/12500000 : ℝ)*x 1 + (210386/390625 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(49126631/100000000 : ℝ), (-858143/12500000 : ℝ), (210386/390625 : ℝ)] ![(225356901683/500000000000 : ℝ), (24808899059/500000000000 : ℝ), (99933676347/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s0_2 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (49126631/100000000 : ℝ)*x 0 + (210386/390625 : ℝ)*x 1 + (-858143/12500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(49126631/100000000 : ℝ), (210386/390625 : ℝ), (-858143/12500000 : ℝ)] ![(225356901683/500000000000 : ℝ), (99933676347/200000000000 : ℝ), (24808899059/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s0_3 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (51355679/100000000 : ℝ)*x 0 + (30400459/100000000 : ℝ)*x 1 + (30400459/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(51355679/100000000 : ℝ), (30400459/100000000 : ℝ), (30400459/100000000 : ℝ)] ![(473705351311/1000000000000 : ℝ), (32893414579/125000000000 : ℝ), (32893414579/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s0_4 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-3164461/20000000 : ℝ)*x 0 + (4776513/10000000 : ℝ)*x 1 + (2388257/5000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-3164461/20000000 : ℝ), (4776513/10000000 : ℝ), (2388257/5000000 : ℝ)] ![(126535253677/1000000000000 : ℝ), (436732310611/1000000000000 : ℝ), (54591551641/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s0_5 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (54503757/100000000 : ℝ)*x 0 + (-7755297/100000000 : ℝ)*x 1 + (47765127/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(54503757/100000000 : ℝ), (-7755297/100000000 : ℝ), (47765127/100000000 : ℝ)] ![(12659546199/25000000000 : ℝ), (56885856999/1000000000000 : ℝ), (436732279857/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s0_6 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (54503743/100000000 : ℝ)*x 0 + (23882571/50000000 : ℝ)*x 1 + (-242353/3125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(54503743/100000000 : ℝ), (23882571/50000000 : ℝ), (-242353/3125000 : ℝ)] ![(506381702123/1000000000000 : ℝ), (436732433631/1000000000000 : ℝ), (2275433951/40000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s0_7 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (844597/12500000 : ℝ)*x 0 + (6442713/12500000 : ℝ)*x 1 + (51541723/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(844597/12500000 : ℝ), (6442713/12500000 : ℝ), (51541723/100000000 : ℝ)] ![(9748095207/200000000000 : ℝ), (9512593147/20000000000 : ℝ), (29726865871/62500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s0_8 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2440277/20000000 : ℝ)*x 0 + (20412597/50000000 : ℝ)*x 1 + (57644017/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-2440277/20000000 : ℝ), (20412597/50000000 : ℝ), (57644017/100000000 : ℝ)] ![(94552027037/1000000000000 : ℝ), (183120957393/500000000000 : ℝ), (16850188861/31250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s0_9 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (9660053/20000000 : ℝ)*x 0 + (-1428823/50000000 : ℝ)*x 1 + (57644013/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(9660053/20000000 : ℝ), (-1428823/50000000 : ℝ), (57644013/100000000 : ℝ)] ![(1105555049/2500000000 : ℝ), (18571968339/1000000000000 : ℝ), (337003751/625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s0_10 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (48300271/100000000 : ℝ)*x 0 + (5764401/10000000 : ℝ)*x 1 + (-1428821/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(48300271/100000000 : ℝ), (5764401/10000000 : ℝ), (-1428821/50000000 : ℝ)] ![(55277760149/125000000000 : ℝ), (539205970137/1000000000000 : ℝ), (2321492399/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s0_11 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (9301767/12500000 : ℝ)*x 0 + (17428273/100000000 : ℝ)*x 1 + (3485653/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(9301767/12500000 : ℝ), (17428273/100000000 : ℝ), (3485653/20000000 : ℝ)] ![(358978577331/500000000000 : ℝ), (141021452979/1000000000000 : ℝ), (352553451/2500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s0_12 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1187873/100000000 : ℝ)*x 0 + (11828129/20000000 : ℝ)*x 1 + (5987707/12500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-1187873/100000000 : ℝ), (11828129/20000000 : ℝ), (5987707/12500000 : ℝ)] ![(6940788333/1000000000000 : ℝ), (277463516503/500000000000 : ℝ), (219066082193/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s0_13 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1700417/3125000 : ℝ)*x 0 + (-3849783/50000000 : ℝ)*x 1 + (9580331/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(1700417/3125000 : ℝ), (-3849783/50000000 : ℝ), (9580331/20000000 : ℝ)] ![(505440117391/1000000000000 : ℝ), (705346427/12500000000 : ℝ), (438132154131/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s0_14 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1700417/3125000 : ℝ)*x 0 + (5987707/12500000 : ℝ)*x 1 + (-1924891/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(1700417/3125000 : ℝ), (5987707/12500000 : ℝ), (-1924891/25000000 : ℝ)] ![(505440117391/1000000000000 : ℝ), (219066082193/500000000000 : ℝ), (28213848863/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s0_15 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3941571/50000000 : ℝ)*x 0 + (10219399/20000000 : ℝ)*x 1 + (51096993/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(3941571/50000000 : ℝ), (10219399/20000000 : ℝ), (51096993/100000000 : ℝ)] ![(57938325253/1000000000000 : ℝ), (235515420213/500000000000 : ℝ), (235515409877/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem base_bounds_w017_s0 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (X : Fin 3 → Fin 3 → ℝ)
    (hS : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2) ≤ 3)
    (hT : lpNorm p (X 0+X 1+X 2) ≤ (27651/20000 : ℝ))
    (hC : lpNorm p (X 0+X 1+X 2) ≤ (368989/100000 : ℝ)*(X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1)+(-381679833/20000000 : ℝ)) :
    -(8681/10000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(4883/10000 : ℝ) ∧ (1919/2500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (11063/10000 : ℝ) := by

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

  have h25 := support_w017_s0_0 p hpa hpb (X 0)

  have h26 := support_w017_s0_1 p hpa hpb (X 1)

  have h27 := support_w017_s0_2 p hpa hpb (X 2)

  have h28 := (support_w017_s0_3 p hpa hpb (X 0+X 1+X 2)).trans hT
  simp only [Pi.add_apply] at h28

  have h29 := (support_w017_s0_3 p hpa hpb (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h29

  have h30 := support_w017_s0_4 p hpa hpb (X 0)

  have h31 := support_w017_s0_5 p hpa hpb (X 1)

  have h32 := support_w017_s0_6 p hpa hpb (X 2)

  have h34 := (support_w017_s0_7 p hpa hpb (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h34

  have h35 := support_w017_s0_8 p hpa hpb (X 0)

  have h36 := support_w017_s0_9 p hpa hpb (X 1)

  have h37 := support_w017_s0_10 p hpa hpb (X 2)

  have h38 := (support_w017_s0_11 p hpa hpb (X 0+X 1+X 2)).trans hT
  simp only [Pi.add_apply] at h38

  have h39 := (support_w017_s0_11 p hpa hpb (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h39

  have h40 := support_w017_s0_12 p hpa hpb (X 0)

  have h41 := support_w017_s0_13 p hpa hpb (X 1)

  have h42 := support_w017_s0_14 p hpa hpb (X 2)

  have h43 := (support_w017_s0_15 p hpa hpb (X 0+X 1+X 2)).trans hT
  simp only [Pi.add_apply] at h43

  have h44 := (support_w017_s0_15 p hpa hpb (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h44

  refine ⟨?_,?_,?_,?_⟩

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hu2, hS, h26, h30, h31, h32, h34, h35, h36, h40, h43, h44]

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hS, h25, h26, h27, h28, h29, h43]

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hu1, hS, h27, h29, h30, h35, h36, h37, h38, h39, h40, h41]

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hS, h27, h28, h29, h30, h31, h32, h36, h40, h41, h42, h44]

theorem coupled_box_w017_s0 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (X : Fin 3 → Fin 3 → ℝ)
    (hS : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2) ≤ 3)
    (hT : lpNorm p (X 0+X 1+X 2) ≤ (27651/20000 : ℝ))
    (hC : lpNorm p (X 0+X 1+X 2) ≤ (368989/100000 : ℝ)*(X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1)+(-381679833/20000000 : ℝ)) :
    ∀ j i, if j = i then -(8681/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(4883/10000 : ℝ)
      else (1919/2500 : ℝ) ≤ X j i ∧ X j i ≤ (11063/10000 : ℝ) := by
  exact coordinateBox_of_base_bounds (fun Y hS hT hC => base_bounds_w017_s0 p hpa hpb Y hS hT hC)
    X hS hT hC

end HlawkaSchatten.DiagonalCutoff8

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace HlawkaSchatten.DiagonalCutoff8
open HlawkaSchatten.DiagonalCutoff12
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle
open scoped BigOperators

theorem support_w017_s1_0 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1212273/100000000 : ℝ)*x 0 + (3346829/6250000 : ℝ)*x 1 + (3346829/6250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-1212273/100000000 : ℝ), (3346829/6250000 : ℝ), (3346829/6250000 : ℝ)] ![(710083753/100000000000 : ℝ), (124112393743/250000000000 : ℝ), (124112393743/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s1_1 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6355731/12500000 : ℝ)*x 0 + (-5043503/100000000 : ℝ)*x 1 + (53549263/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(6355731/12500000 : ℝ), (-5043503/100000000 : ℝ), (53549263/100000000 : ℝ)] ![(7319309743/15625000000 : ℝ), (35114598883/1000000000000 : ℝ), (496449564577/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s1_2 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6355731/12500000 : ℝ)*x 0 + (53549263/100000000 : ℝ)*x 1 + (-5043503/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(6355731/12500000 : ℝ), (53549263/100000000 : ℝ), (-5043503/100000000 : ℝ)] ![(7319309743/15625000000 : ℝ), (496449564577/1000000000000 : ℝ), (35114598883/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s1_3 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (48786367/100000000 : ℝ)*x 0 + (1985097/6250000 : ℝ)*x 1 + (635231/2000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(48786367/100000000 : ℝ), (1985097/6250000 : ℝ), (635231/2000000 : ℝ)] ![(55901889689/125000000000 : ℝ), (276392443953/1000000000000 : ℝ), (276392424439/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s1_4 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-12300709/100000000 : ℝ)*x 0 + (49280051/100000000 : ℝ)*x 1 + (49280051/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-12300709/100000000 : ℝ), (49280051/100000000 : ℝ), (49280051/100000000 : ℝ)] ![(47707718841/500000000000 : ℝ), (113073067817/250000000000 : ℝ), (113073067817/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s1_5 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5352167/10000000 : ℝ)*x 0 + (-1775617/25000000 : ℝ)*x 1 + (49280051/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(5352167/10000000 : ℝ), (-1775617/25000000 : ℝ), (49280051/100000000 : ℝ)] ![(31010172141/62500000000 : ℝ), (2061798219/40000000000 : ℝ), (113073067817/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s1_6 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5352167/10000000 : ℝ)*x 0 + (49280051/100000000 : ℝ)*x 1 + (-1775617/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(5352167/10000000 : ℝ), (49280051/100000000 : ℝ), (-1775617/25000000 : ℝ)] ![(31010172141/62500000000 : ℝ), (113073067817/250000000000 : ℝ), (2061798219/40000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s1_7 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2340313/12500000 : ℝ)*x 0 + (2905081/6250000 : ℝ)*x 1 + (2905081/6250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(2340313/12500000 : ℝ), (2905081/6250000 : ℝ), (2905081/6250000 : ℝ)] ![(152814871571/1000000000000 : ℝ), (423592553577/1000000000000 : ℝ), (423592553577/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s1_8 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-9693333/100000000 : ℝ)*x 0 + (11338603/25000000 : ℝ)*x 1 + (55316379/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-9693333/100000000 : ℝ), (11338603/25000000 : ℝ), (55316379/100000000 : ℝ)] ![(36525098463/500000000000 : ℝ), (103023826347/250000000000 : ℝ), (514854485003/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s1_9 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (49748401/100000000 : ℝ)*x 0 + (-128917/3125000 : ℝ)*x 1 + (55316379/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(49748401/100000000 : ℝ), (-128917/3125000 : ℝ), (55316379/100000000 : ℝ)] ![(18284583511/40000000000 : ℝ), (28030907553/1000000000000 : ℝ), (514854485003/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s1_10 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6218549/12500000 : ℝ)*x 0 + (11063279/20000000 : ℝ)*x 1 + (-515667/12500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(6218549/12500000 : ℝ), (11063279/20000000 : ℝ), (-515667/12500000 : ℝ)] ![(91422899011/200000000000 : ℝ), (514854651973/1000000000000 : ℝ), (14015423303/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s1_11 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (60172109/100000000 : ℝ)*x 0 + (3201041/12500000 : ℝ)*x 1 + (6402081/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(60172109/100000000 : ℝ), (3201041/12500000 : ℝ), (6402081/25000000 : ℝ)] ![(113157998583/200000000000 : ℝ), (217105015711/1000000000000 : ℝ), (217104977689/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s1_12 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2657471/100000000 : ℝ)*x 0 + (56989473/100000000 : ℝ)*x 1 + (767331/1562500 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-2657471/100000000 : ℝ), (56989473/100000000 : ℝ), (767331/1562500 : ℝ)] ![(17119655571/1000000000000 : ℝ), (13308649883/25000000000 : ℝ), (225267168499/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s1_13 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5363079/10000000 : ℝ)*x 0 + (-1794769/25000000 : ℝ)*x 1 + (49109169/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(5363079/10000000 : ℝ), (-1794769/25000000 : ℝ), (49109169/100000000 : ℝ)] ![(497297086489/1000000000000 : ℝ), (52168721487/1000000000000 : ℝ), (225267091353/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s1_14 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (53630783/100000000 : ℝ)*x 0 + (24554589/50000000 : ℝ)*x 1 + (-7179073/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(53630783/100000000 : ℝ), (24554589/50000000 : ℝ), (-7179073/100000000 : ℝ)] ![(497297013713/1000000000000 : ℝ), (450534275281/1000000000000 : ℝ), (13042174261/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s1_15 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (17420653/100000000 : ℝ)*x 0 + (47061353/100000000 : ℝ)*x 1 + (11765333/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(17420653/100000000 : ℝ), (47061353/100000000 : ℝ), (11765333/25000000 : ℝ)] ![(35238080923/250000000000 : ℝ), (429523932853/1000000000000 : ℝ), (429523717957/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem base_bounds_w017_s1 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (X : Fin 3 → Fin 3 → ℝ)
    (hS : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2) ≤ 3)
    (hT : lpNorm p (X 0+X 1+X 2) ≤ (27651/20000 : ℝ))
    (hC : lpNorm p (X 0+X 1+X 2) ≤ (368989/100000 : ℝ)*(X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1)+(-19137380627452221/1000000000000000 : ℝ)) :
    -(8027/10000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(1487/2500 : ℝ) ∧ (8321/10000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (2047/2000 : ℝ) := by

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

  have h25 := support_w017_s1_0 p hpa hpb (X 0)

  have h26 := support_w017_s1_1 p hpa hpb (X 1)

  have h27 := support_w017_s1_2 p hpa hpb (X 2)

  have h29 := (support_w017_s1_3 p hpa hpb (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h29

  have h30 := support_w017_s1_4 p hpa hpb (X 0)

  have h31 := support_w017_s1_5 p hpa hpb (X 1)

  have h32 := support_w017_s1_6 p hpa hpb (X 2)

  have h34 := (support_w017_s1_7 p hpa hpb (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h34

  have h35 := support_w017_s1_8 p hpa hpb (X 0)

  have h36 := support_w017_s1_9 p hpa hpb (X 1)

  have h37 := support_w017_s1_10 p hpa hpb (X 2)

  have h38 := (support_w017_s1_11 p hpa hpb (X 0+X 1+X 2)).trans hT
  simp only [Pi.add_apply] at h38

  have h39 := (support_w017_s1_11 p hpa hpb (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h39

  have h40 := support_w017_s1_12 p hpa hpb (X 0)

  have h41 := support_w017_s1_13 p hpa hpb (X 1)

  have h42 := support_w017_s1_14 p hpa hpb (X 2)

  have h44 := (support_w017_s1_15 p hpa hpb (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h44

  refine ⟨?_,?_,?_,?_⟩

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hS, h30, h31, h32, h34, h39, h42, h44]

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hb11.1, hS, h25, h26, h27, h29, h35, h36, h37, h39, h44]

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hb12.2, hu1, hS, h25, h26, h29, h35, h36, h37, h38, h39, h42]

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hb11.1, hb22.1, hu1, hS, h30, h31, h32, h39, h40, h41, h42, h44]

theorem coupled_box_w017_s1 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (X : Fin 3 → Fin 3 → ℝ)
    (hS : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2) ≤ 3)
    (hT : lpNorm p (X 0+X 1+X 2) ≤ (27651/20000 : ℝ))
    (hC : lpNorm p (X 0+X 1+X 2) ≤ (368989/100000 : ℝ)*(X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1)+(-19137380627452221/1000000000000000 : ℝ)) :
    ∀ j i, if j = i then -(8027/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(1487/2500 : ℝ)
      else (8321/10000 : ℝ) ≤ X j i ∧ X j i ≤ (2047/2000 : ℝ) := by
  exact coordinateBox_of_base_bounds (fun Y hS hT hC => base_bounds_w017_s1 p hpa hpb Y hS hT hC)
    X hS hT hC

end HlawkaSchatten.DiagonalCutoff8

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace HlawkaSchatten.DiagonalCutoff8
open HlawkaSchatten.DiagonalCutoff12
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle
open scoped BigOperators

theorem support_w017_s2_0 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1312137/100000000 : ℝ)*x 0 + (53517561/100000000 : ℝ)*x 1 + (26758781/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-1312137/100000000 : ℝ), (53517561/100000000 : ℝ), (26758781/50000000 : ℝ)] ![(1939971971/250000000000 : ℝ), (9922400911/20000000000 : ℝ), (62015006993/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s2_1 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (50865547/100000000 : ℝ)*x 0 + (-1264911/25000000 : ℝ)*x 1 + (53517561/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(50865547/100000000 : ℝ), (-1264911/25000000 : ℝ), (53517561/100000000 : ℝ)] ![(468639310597/1000000000000 : ℝ), (176203121/5000000000 : ℝ), (9922400911/20000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s2_2 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (50865547/100000000 : ℝ)*x 0 + (53517561/100000000 : ℝ)*x 1 + (-1264911/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(50865547/100000000 : ℝ), (53517561/100000000 : ℝ), (-1264911/25000000 : ℝ)] ![(468639310597/1000000000000 : ℝ), (9922400911/20000000000 : ℝ), (176203121/5000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s2_3 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (48577207/100000000 : ℝ)*x 0 + (1991979/6250000 : ℝ)*x 1 + (31871663/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(48577207/100000000 : ℝ), (1991979/6250000 : ℝ), (31871663/100000000 : ℝ)] ![(222532972163/500000000000 : ℝ), (69366755543/250000000000 : ℝ), (277467012411/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s2_4 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-12086911/100000000 : ℝ)*x 0 + (49370291/100000000 : ℝ)*x 1 + (24685147/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-12086911/100000000 : ℝ), (49370291/100000000 : ℝ), (24685147/50000000 : ℝ)] ![(46778988027/500000000000 : ℝ), (113305246887/250000000000 : ℝ), (226610509213/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s2_5 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (334151/625000 : ℝ)*x 0 + (-282471/4000000 : ℝ)*x 1 + (49370293/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(334151/625000 : ℝ), (-282471/4000000 : ℝ), (49370293/100000000 : ℝ)] ![(12389125871/25000000000 : ℝ), (51213951437/1000000000000 : ℝ), (453221008133/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s2_6 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (53464159/100000000 : ℝ)*x 0 + (49370293/100000000 : ℝ)*x 1 + (-3530887/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(53464159/100000000 : ℝ), (49370293/100000000 : ℝ), (-3530887/50000000 : ℝ)] ![(495565024447/1000000000000 : ℝ), (453221008133/1000000000000 : ℝ), (10242788661/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s2_7 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3881213/20000000 : ℝ)*x 0 + (4617439/10000000 : ℝ)*x 1 + (23087197/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(3881213/20000000 : ℝ), (4617439/10000000 : ℝ), (23087197/50000000 : ℝ)] ![(79542067967/500000000000 : ℝ), (420457903349/1000000000000 : ℝ), (105114486047/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s2_8 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-9560901/100000000 : ℝ)*x 0 + (45588333/100000000 : ℝ)*x 1 + (55195073/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-9560901/100000000 : ℝ), (45588333/100000000 : ℝ), (55195073/100000000 : ℝ)] ![(71932130049/1000000000000 : ℝ), (414479109967/1000000000000 : ℝ), (513588749209/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s2_9 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (9964747/20000000 : ℝ)*x 0 + (-2094771/50000000 : ℝ)*x 1 + (27597537/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(9964747/20000000 : ℝ), (-2094771/50000000 : ℝ), (27597537/50000000 : ℝ)] ![(45789077163/100000000000 : ℝ), (28520453917/1000000000000 : ℝ), (513588759641/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s2_10 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1245593/2500000 : ℝ)*x 0 + (55195099/100000000 : ℝ)*x 1 + (-4189529/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(1245593/2500000 : ℝ), (55195099/100000000 : ℝ), (-4189529/100000000 : ℝ)] ![(114472654267/250000000000 : ℝ), (513589020463/1000000000000 : ℝ), (7130088673/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s2_11 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (59407099/100000000 : ℝ)*x 0 + (26031817/100000000 : ℝ)*x 1 + (406747/1562500 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(59407099/100000000 : ℝ), (26031817/100000000 : ℝ), (406747/1562500 : ℝ)] ![(139432758669/250000000000 : ℝ), (55283629753/250000000000 : ℝ), (55283608323/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s2_12 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1374841/50000000 : ℝ)*x 0 + (28424861/50000000 : ℝ)*x 1 + (9837313/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-1374841/50000000 : ℝ), (28424861/50000000 : ℝ), (9837313/20000000 : ℝ)] ![(17787077133/1000000000000 : ℝ), (132720636689/250000000000 : ℝ), (225665182873/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s2_13 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1071627/2000000 : ℝ)*x 0 + (-7144463/100000000 : ℝ)*x 1 + (24593269/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(1071627/2000000 : ℝ), (-7144463/100000000 : ℝ), (24593269/50000000 : ℝ)] ![(124195777369/250000000000 : ℝ), (51886791307/1000000000000 : ℝ), (451330087967/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s2_14 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (53581337/100000000 : ℝ)*x 0 + (983731/2000000 : ℝ)*x 1 + (-446529/6250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(53581337/100000000 : ℝ), (983731/2000000 : ℝ), (-446529/6250000 : ℝ)] ![(3881116987/7812500000 : ℝ), (18053208457/40000000000 : ℝ), (1037735989/20000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem support_w017_s2_15 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3602283/20000000 : ℝ)*x 0 + (23399437/50000000 : ℝ)*x 1 + (46798851/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := norm_support_interval_cert (p := p) (b := (37/4 : ℝ)) 37 33 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(3602283/20000000 : ℝ), (23399437/50000000 : ℝ), (46798851/100000000 : ℝ)] ![(146322531633/1000000000000 : ℝ), (85367769323/200000000000 : ℝ), (426838611411/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h

theorem base_bounds_w017_s2 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (X : Fin 3 → Fin 3 → ℝ)
    (hS : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2) ≤ 3)
    (hT : lpNorm p (X 0+X 1+X 2) ≤ (27651/20000 : ℝ))
    (hC : lpNorm p (X 0+X 1+X 2) ≤ (368989/100000 : ℝ)*(X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1)+(-191393031379989/10000000000000 : ℝ)) :
    -(1599/2000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(1199/2000 : ℝ) ∧ (8353/10000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (5099/5000 : ℝ) := by

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

  have h25 := support_w017_s2_0 p hpa hpb (X 0)

  have h26 := support_w017_s2_1 p hpa hpb (X 1)

  have h27 := support_w017_s2_2 p hpa hpb (X 2)

  have h29 := (support_w017_s2_3 p hpa hpb (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h29

  have h30 := support_w017_s2_4 p hpa hpb (X 0)

  have h31 := support_w017_s2_5 p hpa hpb (X 1)

  have h32 := support_w017_s2_6 p hpa hpb (X 2)

  have h33 := (support_w017_s2_7 p hpa hpb (X 0+X 1+X 2)).trans hT
  simp only [Pi.add_apply] at h33

  have h34 := (support_w017_s2_7 p hpa hpb (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h34

  have h35 := support_w017_s2_8 p hpa hpb (X 0)

  have h36 := support_w017_s2_9 p hpa hpb (X 1)

  have h37 := support_w017_s2_10 p hpa hpb (X 2)

  have h38 := (support_w017_s2_11 p hpa hpb (X 0+X 1+X 2)).trans hT
  simp only [Pi.add_apply] at h38

  have h39 := (support_w017_s2_11 p hpa hpb (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h39

  have h40 := support_w017_s2_12 p hpa hpb (X 0)

  have h41 := support_w017_s2_13 p hpa hpb (X 1)

  have h42 := support_w017_s2_14 p hpa hpb (X 2)

  have h44 := (support_w017_s2_15 p hpa hpb (X 0+X 1+X 2)).trans hC
  simp only [Pi.add_apply] at h44

  refine ⟨?_,?_,?_,?_⟩

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hb20.2, hS, h27, h29, h30, h31, h32, h33, h34, h36, h40, h41]

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hu1, hS, h25, h26, h27, h29, h32, h36, h37, h39, h40]

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hb12.2, hu1, hS, h25, h26, h29, h35, h36, h37, h38, h39, h42]

  · linarith only [hu0, hl0, hb00.1, hb00.2, hb01.1, hb01.2, hb02.1, hb02.2, hu1, hl1, hb10.1, hb10.2, hb11.1, hb11.2, hb12.1, hb12.2, hu2, hl2, hb20.1, hb20.2, hb21.1, hb21.2, hb22.1, hb22.2, hb11.1, hb20.2, hS, h30, h31, h33, h34, h37, h40, h41, h42, h44]

theorem coupled_box_w017_s2 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) (X : Fin 3 → Fin 3 → ℝ)
    (hS : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2) ≤ 3)
    (hT : lpNorm p (X 0+X 1+X 2) ≤ (27651/20000 : ℝ))
    (hC : lpNorm p (X 0+X 1+X 2) ≤ (368989/100000 : ℝ)*(X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1)+(-191393031379989/10000000000000 : ℝ)) :
    ∀ j i, if j = i then -(1599/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(1199/2000 : ℝ)
      else (8353/10000 : ℝ) ≤ X j i ∧ X j i ≤ (5099/5000 : ℝ) := by
  exact coordinateBox_of_base_bounds (fun Y hS hT hC => base_bounds_w017_s2 p hpa hpb Y hS hT hC)
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

theorem lower_w017_000 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (1169/128 : ℝ)) :
    (368989/912500 : ℝ)*p < cyclicConstant p := by

  have ht : (95625973/125000000 : ℝ) ^ (73/8 : ℝ) ≤ (10848281151/125000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (95625973/125000000 : ℝ)) (X := (10848281151/125000000000 : ℝ)) (by norm_num) (by norm_num) 73 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have hA : (260848281151/125000000000 : ℝ) ≤ (270988769331/250000000000 : ℝ) ^ (73/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (270988769331/250000000000 : ℝ)) (X := (260848281151/125000000000 : ℝ)) (by norm_num) 73 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have ha : (3 : ℝ) ≤ (1127943279019/1000000000000 : ℝ) ^ (73/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1127943279019/1000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 73 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  apply HlawkaSchatten.DiagonalCutoff8Scalar.cyclicConstant_lower_endpoint (alpha := (73/8 : ℝ)) (beta := (1169/128 : ℝ))
    (t := (95625973/125000000 : ℝ)) (Aup := (270988769331/250000000000 : ℝ)) (aup := (1127943279019/1000000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower_w017_001 (p : ℝ) (hpa : (1169/128 : ℝ) ≤ p) (hpb : p ≤ (585/64 : ℝ)) :
    (368989/912500 : ℝ)*p < cyclicConstant p := by

  have ht : (95625973/125000000 : ℝ) ^ (1169/128 : ℝ) ≤ (17320963809/200000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (95625973/125000000 : ℝ)) (X := (17320963809/200000000000 : ℝ)) (by norm_num) (by norm_num) 1169 128 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have hA : (417320963809/200000000000 : ℝ) ≤ (270967502399/250000000000 : ℝ) ^ (1169/128 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (270967502399/250000000000 : ℝ)) (X := (417320963809/200000000000 : ℝ)) (by norm_num) 1169 128 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have ha : (3 : ℝ) ≤ (70489194849/62500000000 : ℝ) ^ (1169/128 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (70489194849/62500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 1169 128 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  apply HlawkaSchatten.DiagonalCutoff8Scalar.cyclicConstant_lower_endpoint (alpha := (1169/128 : ℝ)) (beta := (585/64 : ℝ))
    (t := (95625973/125000000 : ℝ)) (Aup := (270967502399/250000000000 : ℝ)) (aup := (70489194849/62500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower_w017_002 (p : ℝ) (hpa : (585/64 : ℝ) ≤ p) (hpb : p ≤ (293/32 : ℝ)) :
    (368989/912500 : ℝ)*p < cyclicConstant p := by

  have ht : (95625973/125000000 : ℝ) ^ (585/64 : ℝ) ≤ (10802971021/125000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (95625973/125000000 : ℝ)) (X := (10802971021/125000000000 : ℝ)) (by norm_num) (by norm_num) 585 64 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have hA : (260802971021/125000000000 : ℝ) ≤ (1083785114601/1000000000000 : ℝ) ^ (585/64 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1083785114601/1000000000000 : ℝ)) (X := (260802971021/125000000000 : ℝ)) (by norm_num) 585 64 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have ha : (3 : ℝ) ≤ (1127711166649/1000000000000 : ℝ) ^ (585/64 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1127711166649/1000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 585 64 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  apply HlawkaSchatten.DiagonalCutoff8Scalar.cyclicConstant_lower_endpoint (alpha := (585/64 : ℝ)) (beta := (293/32 : ℝ))
    (t := (95625973/125000000 : ℝ)) (Aup := (1083785114601/1000000000000 : ℝ)) (aup := (1127711166649/1000000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower_w017_003 (p : ℝ) (hpa : (293/32 : ℝ) ≤ p) (hpb : p ≤ (147/16 : ℝ)) :
    (368989/912500 : ℝ)*p < cyclicConstant p := by

  have ht : (95625973/125000000 : ℝ) ^ (293/32 : ℝ) ≤ (43031400553/500000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (95625973/125000000 : ℝ)) (X := (43031400553/500000000000 : ℝ)) (by norm_num) (by norm_num) 293 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have hA : (1043031400553/500000000000 : ℝ) ≤ (1083615840789/1000000000000 : ℝ) ^ (293/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1083615840789/1000000000000 : ℝ)) (X := (1043031400553/500000000000 : ℝ)) (by norm_num) 293 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have ha : (3 : ℝ) ≤ (1127479893993/1000000000000 : ℝ) ^ (293/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1127479893993/1000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 293 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  apply HlawkaSchatten.DiagonalCutoff8Scalar.cyclicConstant_lower_endpoint (alpha := (293/32 : ℝ)) (beta := (147/16 : ℝ))
    (t := (95625973/125000000 : ℝ)) (Aup := (1083615840789/1000000000000 : ℝ)) (aup := (1127479893993/1000000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower_w017_004 (p : ℝ) (hpa : (147/16 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) :
    (368989/912500 : ℝ)*p < cyclicConstant p := by

  have ht : (95625973/125000000 : ℝ) ^ (147/16 : ℝ) ≤ (85345383649/1000000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (95625973/125000000 : ℝ)) (X := (85345383649/1000000000000 : ℝ)) (by norm_num) (by norm_num) 147 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have hA : (2085345383649/1000000000000 : ℝ) ≤ (1083279343873/1000000000000 : ℝ) ^ (147/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1083279343873/1000000000000 : ℝ)) (X := (2085345383649/1000000000000 : ℝ)) (by norm_num) 147 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have ha : (3 : ℝ) ≤ (1127019849677/1000000000000 : ℝ) ^ (147/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1127019849677/1000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 147 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  apply HlawkaSchatten.DiagonalCutoff8Scalar.cyclicConstant_lower_endpoint (alpha := (147/16 : ℝ)) (beta := (37/4 : ℝ))
    (t := (95625973/125000000 : ℝ)) (Aup := (1083279343873/1000000000000 : ℝ)) (aup := (1127019849677/1000000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem scalar_lower_w017 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) :
    (368989/912500 : ℝ)*p < cyclicConstant p := by

  by_cases h0 : p ≤ (1169/128 : ℝ)
  · exact lower_w017_000 p (by linarith) h0

  by_cases h1 : p ≤ (585/64 : ℝ)
  · exact lower_w017_001 p (by linarith) h1

  by_cases h2 : p ≤ (293/32 : ℝ)
  · exact lower_w017_002 p (by linarith) h2

  by_cases h3 : p ≤ (147/16 : ℝ)
  · exact lower_w017_003 p (by linarith) h3

  exact lower_w017_004 p (by linarith) hpb

theorem envelope_w017 (p : ℝ) (hp : (73/8 : ℝ) ≤ p) :
    scalarEnvelope p (9217/20000 : ℝ) < (368989/912500 : ℝ)*p := by

  have hq : (9217/20000 : ℝ) ^ (73/8 : ℝ) ≤ (170220269/200000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (9217/20000 : ℝ)) (X := (170220269/200000000000 : ℝ)) (by norm_num) (by norm_num) 73 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  have hb : (500444309409/1000000000000 : ℝ) ≤ (2601/2806 : ℝ) ^ (73/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2601/2806 : ℝ)) (X := (500444309409/1000000000000 : ℝ)) (by norm_num) 73 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num

  apply envelope_linear_of_certificate (73/8 : ℝ) (by norm_num) hp
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he : (1-((1-(9217/20000 : ℝ))/(2*(368989/912500 : ℝ)))/(73/8 : ℝ) : ℝ) = (2601/2806 : ℝ) := by norm_num
  rw [he]
  linarith only [hq, hb]

end HlawkaSchatten.DiagonalCutoff8

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace HlawkaSchatten.DiagonalCutoff8
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
open HlawkaSchatten.DiagonalCutoff8Scalar
theorem curvature_w017 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) :
    p * (1382187197400382254843/121978638670652371685 : ℝ) * (116217153/291051932 : ℝ) ^ (p-2) < 1 ∧
    (509450957519148694419048540045/27234457159423064654400563728 : ℝ) * (4665330/10015247 : ℝ) ^ (p-2) < 2*(368989/925000 : ℝ)-1/p := by
  have hp0 : 0 < p := by linarith

  have hrT : (116217153/291051932 : ℝ) ^ (p-2) ≤ (116217153/291051932 : ℝ) ^ (7 : ℕ) := by
    have h := Real.rpow_le_rpow_of_exponent_ge' (x := (116217153/291051932 : ℝ))
      (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) ≤ 7) (by linarith : (7 : ℝ) ≤ p-2)
    calc _ ≤ (116217153/291051932 : ℝ) ^ ((7 : ℕ) : ℝ) := h
         _ = _ := Real.rpow_natCast _ _

  have hrC : (4665330/10015247 : ℝ) ^ (p-2) ≤ (4665330/10015247 : ℝ) ^ (7 : ℕ) := by
    have h := Real.rpow_le_rpow_of_exponent_ge' (x := (4665330/10015247 : ℝ))
      (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) ≤ 7) (by linarith : (7 : ℝ) ≤ p-2)
    calc _ ≤ (4665330/10015247 : ℝ) ^ ((7 : ℕ) : ℝ) := h
         _ = _ := Real.rpow_natCast _ _

  constructor
  · have h1 := mul_le_mul_of_nonneg_left hrT (show 0 ≤ p*(1382187197400382254843/121978638670652371685 : ℝ) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hpb (show 0 ≤ (1382187197400382254843/121978638670652371685 : ℝ)*((116217153/291051932 : ℝ) ^ (7 : ℕ)) by norm_num)
    have hend : (37/4 : ℝ)*(1382187197400382254843/121978638670652371685 : ℝ)*((116217153/291051932 : ℝ) ^ (7 : ℕ)) < 1 := by norm_num
    nlinarith only [h1,h2,hend]
  · have h1 := mul_le_mul_of_nonneg_left hrC (show 0 ≤ (509450957519148694419048540045/27234457159423064654400563728 : ℝ) by norm_num)
    have hinv : 1/p ≤ 1/(73/8 : ℝ) := one_div_le_one_div_of_le (by norm_num) hpa
    have hend : (509450957519148694419048540045/27234457159423064654400563728 : ℝ)*((4665330/10015247 : ℝ) ^ (7 : ℕ)) < 2*(368989/925000 : ℝ)-1/(73/8 : ℝ) := by norm_num
    linarith only [h1,hinv,hend]

theorem localized_nonnegative_w017 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hS : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2) = 3)
    (hT1 : 1 ≤ lpNorm p (X 0+X 1+X 2)) (hT : lpNorm p (X 0+X 1+X 2) ≤ (27651/20000 : ℝ))
    (hC : lpNorm p (X 0+X 1+X 2) ≤ (368989/100000 : ℝ)*(X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1)+(-191393031379989/10000000000000 : ℝ)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  have hKlo := scalar_lower_w017 p hpa hpb
  have hKhi := cyclicConstant_upper8 (by linarith : 8 ≤ p) (by linarith : p ≤ 12)
  have hbox := coupled_box_w017_s2 p hpa hpb X hS.le hT hC
  have hrows := rows_norm_cap 9 (by norm_num) (by linarith : (9 : ℝ) ≤ p)
    (by norm_num : (0 : ℝ) ≤ (1199/2000 : ℝ)) (by norm_num : (0 : ℝ) ≤ (1599/2000 : ℝ))
    (by norm_num : (0 : ℝ) ≤ (8353/10000 : ℝ)) (by norm_num : (0 : ℝ) ≤ (5099/5000 : ℝ))
    (by norm_num : (0 : ℝ) < (111/100 : ℝ)) (by norm_num) (by norm_num) (by norm_num) X hbox
  have hoff : (201393031379989/36898900000000 : ℝ) ≤ (X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1) := by
    have h := offsum_floor_from_total (k := (368989/100000 : ℝ)) (eps := (333/100000000 : ℝ))
      (W := (X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1)) (by norm_num) hT1
      (by norm_num at hC ⊢; linarith only [hC])
    norm_num at h
    exact h
  have hpairs : ∀ i j l : Fin 3, i ≠ j → i ≠ l → j ≠ l →
      (8353/5000 : ℝ) ≤ X j i+X l i := by
    intro i j l hij hil hjl
    have hj := hbox j i
    have hl := hbox l i
    simp only [if_neg hij.symm] at hj
    simp only [if_neg hil.symm] at hl
    linarith only [hj.1,hl.1]
  obtain ⟨hNT,hNC⟩ := curvature_w017 p hpa hpb
  apply HlawkaSchatten.DiagonalCutoff8.nonnegative_of_curvature_margins
    (c := (368989/925000 : ℝ)) (ell := (1199/2000 : ℝ)) (u := (1599/2000 : ℝ)) (v := (8353/10000 : ℝ)) (w := (5099/5000 : ℝ)) (U := (111/100 : ℝ)) (A := (27651/20000 : ℝ)) (J := (8353/5000 : ℝ)) (W0 := (201393031379989/36898900000000 : ℝ)) (m := (1199/2000 : ℝ)) (M := (5099/5000 : ℝ)) (L := (8353/5000 : ℝ)) (s := (8711/10000 : ℝ)) (t := (27651/20000 : ℝ)) (eta := (4203/10000 : ℝ)) (eps1 := (2 : ℝ)) (eps2 := (1/2 : ℝ)) (gT := (399895033785507144/14602973622728645 : ℝ)) (gC := (917929653187655305259546919/16302201101055348170956880 : ℝ))
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

theorem real_three_w017 (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  intro x y z
  by_contra hf
  have hneg : hlawkaDeficit p (cyclicConstant p) x y z < 0 := by
    rw [HlawkaSchatten.DiagonalConstruction.hlawkaDeficit_eq]
    exact sub_neg.mpr (lt_of_not_ge hf)
  have hlower := scalar_lower_w017 p hpa hpb
  have hK : (368989/100000 : ℝ) ≤ cyclicConstant p := by nlinarith
  have henv := (envelope_w017 p hpa).trans hlower
  obtain ⟨X,hS,hT1,hT,htails0,hfX⟩ := coarse_failure_reduction
    (by linarith : 8 ≤ p) (by norm_num : (0 : ℝ) < (9217/20000 : ℝ))
    (by norm_num) (by linarith) henv x y z hneg
  norm_num at hT
  have hC0 : lpNorm p (X 0+X 1+X 2) ≤ (368989/100000 : ℝ)*(X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1)+(-381679833/20000000 : ℝ) := by
    have h := coupled_relation_of_failure (eps := (1/200 : ℝ))
      (by linarith : (1 : ℝ) ≤ p) (by norm_num : (0 : ℝ) < (368989/100000 : ℝ)) hK X hS htails0 hfX
    norm_num at h ⊢
    linarith only [h]
  have hbox0 := coupled_box_w017_s0 p hpa hpb X hS.le hT hC0
  have htails1 := pair_tail_of_box (rho := (12299/30704 : ℝ)) (eps := (1770037/10000000000 : ℝ))
    9 (by norm_num) (by linarith : (9 : ℝ) ≤ p)
    (by norm_num : (0 : ℝ) ≤ (1919/2500 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) X hS.le hT hbox0
  have hC1 : lpNorm p (X 0+X 1+X 2) ≤ (368989/100000 : ℝ)*(X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1)+(-19137380627452221/1000000000000000 : ℝ) := by
    have h := coupled_relation_of_failure (eps := (1770037/10000000000 : ℝ))
      (by linarith : (1 : ℝ) ≤ p) (by norm_num : (0 : ℝ) < (368989/100000 : ℝ)) hK X hS htails1 hfX
    norm_num at h ⊢
    linarith only [h]
  have hbox1 := coupled_box_w017_s1 p hpa hpb X hS.le hT hC1
  have htails2 := pair_tail_of_box (rho := (4287/16642 : ℝ)) (eps := (333/100000000 : ℝ))
    9 (by norm_num) (by linarith : (9 : ℝ) ≤ p)
    (by norm_num : (0 : ℝ) ≤ (8321/10000 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) X hS.le hT hbox1
  have hC2 : lpNorm p (X 0+X 1+X 2) ≤ (368989/100000 : ℝ)*(X 0 1+X 0 2+X 1 0+X 1 2+X 2 0+X 2 1)+(-191393031379989/10000000000000 : ℝ) := by
    have h := coupled_relation_of_failure (eps := (333/100000000 : ℝ))
      (by linarith : (1 : ℝ) ≤ p) (by norm_num : (0 : ℝ) < (368989/100000 : ℝ)) hK X hS htails2 hfX
    norm_num at h ⊢
    linarith only [h]
  exact (not_lt_of_ge (localized_nonnegative_w017 p hpa hpb X hS hT1 hT hC2)) hfX

end HlawkaSchatten.DiagonalCutoff8


theorem solution (p : ℝ) (hpa : (73/8 : ℝ) ≤ p) (hpb : p ≤ (37/4 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  exact HlawkaSchatten.DiagonalCutoff8.real_three_w017 p hpa hpb

#print axioms solution
