-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Equi.measurableSet_infDomain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:48:34.105366+00:00
-- url     : https://prove2.me/submissions/fc894671-8eba-43d6-bcbb-634e125f39f8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdeleHaarMapEqScaledVolume
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ArchimedeanFundamentalDomainIntegers
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_measurable_infToMixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Equi
open GlobalTheory.CompanionTheory.SW.RealCoord
variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
namespace GlobalTheory.CompanionTheory.Equi
theorem _root_.solution : MeasurableSet (infDomain F) := measurable_infToMixed F (ZSpan.fundamentalDomain_measurableSet (mixedEmbedding.latticeBasis F))
end GlobalTheory.CompanionTheory.Equi
