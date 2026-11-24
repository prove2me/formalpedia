-- Prove2me | solution 1 for GlobalTheory.ClassFin.HarmMin.deriv_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:10:49.247893+00:00
-- url     : https://prove2.me/submissions/3f2d0a55-5248-4aa5-b238-fa3a1e43bfef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HermitianLogTraceSqFirstVariationBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MulLogEqNegLogMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsHermitianLogOfPosDefGramStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SumHermitianLogGramEqZeroOfEnergyMinimum
import Theorems.Thm_GlobalTheory_ClassFin_HarmMin_deriv_entry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin GlobalTheory.ClassFin.HarmMin
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.ClassFin.HarmMin
theorem _root_.solution {Y : ℝ → Matrix ι ι ℂ} {D : Matrix ι ι ℂ} (h : HasDerivAt Y D 0) (h0 : Y 0 = 0)
    (M : Matrix ι ι ℂ) (C : ℝ) :
    HasDerivAt (fun t => 2 * (Matrix.trace (M * Y t)).re + C * ∑ i, ∑ j, ‖Y t i j‖ ^ 2)
      (2 * (Matrix.trace (M * D)).re) 0 := by
  let L : Matrix ι ι ℂ →ₗ[ℝ] ℝ := Complex.reLm ∘ₗ Matrix.traceLinearMap ι ℝ ℂ
  have h1 : HasDerivAt (fun t => (Matrix.trace (M * Y t)).re) (Matrix.trace (M * D)).re 0 :=
    (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (h.const_mul M)
  have h2 : HasDerivAt (fun t => ∑ i, ∑ j, ‖Y t i j‖ ^ 2) (∑ i : ι, ∑ j : ι, (0 : ℝ)) 0 := by
    refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
    have := (deriv_entry h i j).norm_sq
    simpa [h0] using this
  have := (h1.const_mul 2).add (h2.const_mul C)
  simp only [Finset.sum_const_zero, mul_zero, add_zero] at this
  exact this
end GlobalTheory.ClassFin.HarmMin
