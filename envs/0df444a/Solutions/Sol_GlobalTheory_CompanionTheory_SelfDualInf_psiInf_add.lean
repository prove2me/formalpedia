-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SelfDualInf.psiInf_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:40:23.217891+00:00
-- url     : https://prove2.me/submissions/98e35d1a-d3e9-4664-8c9d-592fca7b0e25

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_BijectiveLinearCombinationOfRankAtStalk
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_SelfDualLatticeFiltrationCharacter
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_HasCoordOfFiniteDimensional

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SelfDualInf
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.SelfDualInf
theorem _root_.solution (ψ : AddChar (AF F) ℂ) (x y : Ainf F) :
    psiInf F ψ (x + y) = psiInf F ψ x * psiInf F ψ y := by
  unfold psiInf
  rw [← AddChar.map_add_eq_mul]
  congr 1
  exact Prod.ext rfl (add_zero _).symm
end GlobalTheory.CompanionTheory.SelfDualInf
