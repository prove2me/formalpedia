-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SelfDualInf.hasCoord_ainf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:04:06.785698+00:00
-- url     : https://prove2.me/submissions/b343ced4-1ed7-433c-8385-686ac02ab074

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_BijectiveLinearCombinationOfRankAtStalk
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_SelfDualLatticeFiltrationCharacter
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_HasCoordOfFiniteDimensional
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_HasCoord_of_equiv
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_hasCoord_of_finiteDimensional

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
theorem _root_.solution (hF : IsTotallyReal F) : HasCoord (Ainf F) := by
  let ρ := fun w : InfinitePlace F => InfinitePlace.Completion.ringEquivRealOfIsReal (hF.isReal w)
  have h1 : ∀ w, Continuous (ρ w) := fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (hF.isReal w)).continuous
  have h2 : ∀ w, Continuous (ρ w).symm := fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (hF.isReal w)).symm.continuous
  exact HasCoord.of_equiv (AddEquiv.piCongrRight fun w => (ρ w).toAddEquiv)
    (continuous_pi fun w => (h1 w).comp (continuous_apply w))
    (continuous_pi fun w => (h2 w).comp (continuous_apply w))
    (hasCoord_of_finiteDimensional (InfinitePlace F → ℝ))
end GlobalTheory.CompanionTheory.SelfDualInf
