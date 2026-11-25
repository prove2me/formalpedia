-- Prove2me | solution 1 for GlobalTheory.Jet.norm_polyDeriv_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:47:19.145872+00:00
-- url     : https://prove2.me/submissions/2691b901-ca79-4b74-aa04-5a2e747f176d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardToMultisetEqDegree
import Theorems.Thm_GlobalTheory_Jet_degree_eq_of_mem_support
import Theorems.Thm_GlobalTheory_Jet_polyDeriv_eq_sum_monomial
import Theorems.Thm_GlobalTheory_Jet_polyDeriv_comp_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_gCauchy


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
open GlobalTheory.Jet
variable {σ W W' : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup W'] [NormedSpace ℂ W']
variable {ι : Type} [Fintype ι]
open Classical
namespace GlobalTheory.Jet
theorem _root_.solution (q : ℕ) (hq : 1 ≤ q) (F : EuclideanSpace ℂ ι → ℂ)
    (hF : Differentiable ℂ F) (S : ℝ)
    (hS : ∀ v, ‖F v‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖v‖ ^ 2) ≤ S) (P : MvPolynomial ι ℂ) (a : ℕ)
    (hP : P.IsHomogeneous a) :
    ‖polyDeriv P (fun i => EuclideanSpace.single i 1) F 0‖ ≤
      (∑ m ∈ P.support, ‖P.coeff m‖) * Real.sqrt S *
        (q * Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  set t : ℝ := Real.sqrt q with ht
  have ht0 : 0 < t := Real.sqrt_pos.mpr hq0
  have ht2 : t ^ 2 = q := Real.sq_sqrt hq0.le
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
  set G : EuclideanSpace ℂ ι → ℂ := fun v => F ((t : ℂ)⁻¹ • v) with hGdef
  have hG : Differentiable ℂ G := hF.comp (g := F) (f := fun v => (t : ℂ)⁻¹ • v) (by fun_prop)
  have hGS : ∀ v, ‖G v‖ ^ 2 * Real.exp (-Real.pi * ‖v‖ ^ 2) ≤ S := by
    intro v
    have h := hS ((t : ℂ)⁻¹ • v)
    have e : -(q * Real.pi) * ‖(t : ℂ)⁻¹ • v‖ ^ 2 = -Real.pi * ‖v‖ ^ 2 := by
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ht0.le, mul_pow, inv_pow, ht2]
      field_simp
    rwa [e] at h
  have hFG : F = fun v => G ((t : ℂ) • v) := by
    funext v
    simp only [hGdef, smul_smul, inv_mul_cancel₀ htc, one_smul]
  have hb : ‖polyDeriv P (fun i => EuclideanSpace.single i 1) G 0‖ ≤
      (∑ m ∈ P.support, ‖P.coeff m‖) * (Real.sqrt S *
        (Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2)) := by
    rw [polyDeriv_eq_sum_monomial, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have h := gCauchy ι G hG S hGS m
    rwa [degree_eq_of_mem_support hP hm] at h
  have hpow : t ^ a = (q : ℝ) ^ ((a : ℝ) / 2) := by
    rw [ht, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le]
    congr 1
    ring
  have hsplit : ((q : ℝ) * Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) =
      t ^ a * (Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) := by
    rw [hpow, ← Real.mul_rpow hq0.le (by positivity)]
    congr 1
    ring
  rw [hFG, polyDeriv_comp_smul hP _ _ hG, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg ht0.le, hsplit]
  calc t ^ a * ‖polyDeriv P (fun i => EuclideanSpace.single i 1) G 0‖
      ≤ t ^ a * ((∑ m ∈ P.support, ‖P.coeff m‖) * (Real.sqrt S *
        (Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2))) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring
end GlobalTheory.Jet
