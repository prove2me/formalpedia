-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegLoc.LevelId.red_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:57:21.686129+00:00
-- url     : https://prove2.me/submissions/3421afb0-d5c1-4315-bc43-a9320d552015

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianRepCountFourierExpansion
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_LevelId_red_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_LevelId_red_cT

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
theorem _root_.solution (σ : R →+* R) (ϖ : R) (h : σ ϖ = ϖ) (k : ℕ) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) R) (x : Matrix (Fin m) (Fin n) R) :
    red ϖ k (cT σ x * S * x) = cT (barσ σ ϖ h k) (red ϖ k x) * red ϖ k S * red ϖ k x := by
  rw [red_mul, red_mul, red_cT σ ϖ h]
end GlobalTheory.CompanionTheory.SiegLoc.LevelId
