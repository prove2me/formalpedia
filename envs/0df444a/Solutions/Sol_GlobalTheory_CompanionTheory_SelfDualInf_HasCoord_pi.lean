-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SelfDualInf.HasCoord.pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:06:30.189927+00:00
-- url     : https://prove2.me/submissions/7d451759-c22d-4ab6-b565-2225503aefe4

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
namespace GlobalTheory.CompanionTheory.SelfDualInf
namespace HasCoord
theorem _root_.solution {V : Type} [AddCommGroup V] [TopologicalSpace V] (h : HasCoord V)
    (ι : Type) [Fintype ι] : HasCoord (ι → V) := by
  obtain ⟨N, f, g1, g2⟩ := h
  refine HasCoord.of_equiv (AddEquiv.piCongrRight fun _ : ι => f) ?_ ?_
    (hasCoord_of_finiteDimensional (ι → Fin N → ℝ))
  · exact continuous_pi fun i => g1.comp (continuous_apply i)
  · exact continuous_pi fun i => g2.comp (continuous_apply i)
end HasCoord
end GlobalTheory.CompanionTheory.SelfDualInf
