-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.SizeInt.secondCountable_Ainf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:32:18.706646+00:00
-- url     : https://prove2.me/submissions/e5b3054c-3338-4b94-8638-45da31be9a44

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SizeFunctionRapidDecayIntegrable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.SizeInt
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.SizeInt
theorem _root_.solution (hF : IsTotallyReal F) : SecondCountableTopology (Ainf F) := by
  haveI : ∀ v : InfinitePlace F, SecondCountableTopology v.Completion := fun v =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (hF.isReal v)).toHomeomorph.secondCountableTopology
  exact inferInstanceAs (SecondCountableTopology (∀ v : InfinitePlace F, v.Completion))
end GlobalTheory.CompanionTheory.SW.SizeInt
