-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SelfDualInf.HasCoord.of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:42:48.351325+00:00
-- url     : https://prove2.me/submissions/1909343b-5c40-4afb-8ac0-0fc2d957fdd7

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
theorem _root_.solution {V W : Type} [AddCommGroup V] [TopologicalSpace V] [AddCommGroup W]
    [TopologicalSpace W] (e : V ≃+ W) (h1 : Continuous e) (h2 : Continuous e.symm)
    (h : HasCoord W) : HasCoord V := by
  obtain ⟨N, f, g1, g2⟩ := h
  exact ⟨N, e.trans f, g1.comp h1, h2.comp g2⟩
end HasCoord
end GlobalTheory.CompanionTheory.SelfDualInf
