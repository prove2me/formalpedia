-- Prove2me | solution 1 for GlobalTheory.Phase.transS_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:47:55.202119+00:00
-- url     : https://prove2.me/submissions/e8be3a3e-46cf-4769-9261-9d32c38bff24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitarySiegelThetaTransformationLawStandar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocyclStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EqOfSiegelThetaSeriesRationalEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TransSUnique
import Theorems.Thm_GlobalTheory_SW_I_mem_siegel
import Theorems.Thm_GlobalTheory_T_eq_of_siegelThetaSeriesRational_eq
import Theorems.Thm_GlobalTheory_T_symplecticSiegelAction_mem_upperHalfSpace_and_cocycle


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
open GlobalTheory GlobalTheory.Phase
namespace GlobalTheory.Phase
theorem _root_.solution {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
    {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ} (hσ : σ ∈ Matrix.symplecticGroup ι ℚ)
    {φ ψ ψ' : Matrix κ ι ℚ → ℂ} (hψ : IsSB ψ) (hψ' : IsSB ψ') (h : TransS σ φ ψ)
    (h' : TransS σ φ ψ') : ψ = ψ' := by
  obtain ⟨hd, hs, -⟩ := GlobalTheory.T.symplecticSiegelAction_mem_upperHalfSpace_and_cocycle ι σ hσ _ I_mem_siegel
  refine GlobalTheory.T.eq_of_siegelThetaSeriesRational_eq κ ι ψ ψ' hψ hψ' _ hs fun ζ => ?_
  have e1 := h _ I_mem_siegel fun k => ζ k ᵥ* spDen σ (I • 1)
  have e2 := h' _ I_mem_siegel fun k => ζ k ᵥ* spDen σ (I • 1)
  have e := e1.trans e2.symm
  simpa only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (Ne.isUnit hd),
    Matrix.vecMul_one] using e
end GlobalTheory.Phase
