-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegLoc.LevelId.cT_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:37:32.558232+00:00
-- url     : https://prove2.me/submissions/3001bb45-1b6c-432f-9b31-33edee55b7b3

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianRepCountFourierExpansion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegLoc GlobalTheory.CompanionTheory.SiegLoc.LevelId
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.SiegLoc.LevelId
theorem _root_.solution (σ : R →+* R) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) R) :
    cT σ (x - y) = cT σ x - cT σ y := by
  ext i j
  exact map_sub σ (x j i) (y j i)
end GlobalTheory.CompanionTheory.SiegLoc.LevelId
