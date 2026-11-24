-- Prove2me | solution 1 for GlobalTheory.Phase.ParabValues.trans_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:41:24.224368+00:00
-- url     : https://prove2.me/submissions/de3adbc8-412a-4075-91e5-04d761be50b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EqOfSiegelThetaSeriesRationalEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocycl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationSiegelParabolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelParabolicTransformPhase
import Theorems.Thm_GlobalTheory_SW_I_mem_siegel
import Theorems.Thm_GlobalTheory_SW_eq_of_thS_eq
import Theorems.Thm_GlobalTheory_SiegelAction_symplectic_action


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.ParabValues
open GlobalTheory.SW.Parab
namespace GlobalTheory.Phase.ParabValues
theorem _root_.solution (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι]
    (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) (hσ : σ ∈ Matrix.symplecticGroup ι ℚ)
    (φ ψ ψ' : Matrix κ ι ℚ → ℂ) (hψ : IsSB ψ) (hψ' : IsSB ψ') (h : TransS σ φ ψ)
    (h' : TransS σ φ ψ') : ψ = ψ' := by
  obtain ⟨hd, hs, -⟩ := GlobalTheory.SiegelAction.symplectic_action ι σ hσ _ (I_mem_siegel (ι := ι))
  refine GlobalTheory.SW.eq_of_thS_eq κ ι ψ ψ' hψ hψ' _ hs fun ζ => ?_
  have e : ζ = fun k => (ζ k ᵥ* spDen σ (I • (1 : Matrix ι ι ℂ))) ᵥ*
      (spDen σ (I • (1 : Matrix ι ι ℂ)))⁻¹ := by
    funext k
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd),
      Matrix.vecMul_one]
  rw [e, h _ I_mem_siegel, h' _ I_mem_siegel]
end GlobalTheory.Phase.ParabValues
