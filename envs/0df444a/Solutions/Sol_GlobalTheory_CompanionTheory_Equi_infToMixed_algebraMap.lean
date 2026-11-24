-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Equi.infToMixed_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:28:55.630803+00:00
-- url     : https://prove2.me/submissions/33723704-658c-4945-9218-b447a4aed0db

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdeleHaarMapEqScaledVolume
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ArchimedeanFundamentalDomainIntegers
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RealCoord_toMixed_coord_algebraMap


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
theorem _root_.solution (x : F) :
    infToMixed F (algebraMap F (Ainf F) x) = mixedEmbedding F x := toMixed_coord_algebraMap F x
end GlobalTheory.CompanionTheory.Equi
