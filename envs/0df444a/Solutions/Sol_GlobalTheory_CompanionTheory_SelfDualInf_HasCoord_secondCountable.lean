-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SelfDualInf.HasCoord.secondCountable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:41:39.771845+00:00
-- url     : https://prove2.me/submissions/457c1c03-40bb-4a52-8311-fc687b6ff48d

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
namespace GlobalTheory.CompanionTheory.SelfDualInf
namespace HasCoord
theorem _root_.solution {V : Type} [AddCommGroup V] [TopologicalSpace V]
    (h : HasCoord V) : SecondCountableTopology V := by
  obtain ⟨N, e, g1, g2⟩ := h
  exact (Homeomorph.mk e.toEquiv g1 g2).secondCountableTopology
end HasCoord
end GlobalTheory.CompanionTheory.SelfDualInf
