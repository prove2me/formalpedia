-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Equi.infToMixed_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:28:55.767856+00:00
-- url     : https://prove2.me/submissions/ca1a76fc-1e70-4f6d-8cfa-260074530ed1

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdeleHaarMapEqScaledVolume
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ArchimedeanFundamentalDomainIntegers
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RealCoord_toMixed_add


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
theorem _root_.solution (x y : Ainf F) : infToMixed F (x + y) = infToMixed F x + infToMixed F y := by
  show toMixed F (coord F (x + y)) = toMixed F (coord F x) + toMixed F (coord F y)
  rw [map_add, toMixed_add]
end GlobalTheory.CompanionTheory.Equi
