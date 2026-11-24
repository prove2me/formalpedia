-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegLoc.LevelId.neg_mem_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:57:19.386917+00:00
-- url     : https://prove2.me/submissions/2067b8a6-e1de-45fa-b98c-1dc575d24513

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianRepCountFourierExpansion
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_LevelId_red_neg

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
theorem _root_.solution (σ : R →+* R) (ϖ : R) (n k : ℕ) {B : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)}
    (hB : B ∈ hermMod σ ϖ n k) : -B ∈ hermMod σ ϖ n k := by
  unfold hermMod at hB ⊢
  obtain ⟨h0, hh, rfl⟩ := hB
  refine ⟨-h0, ?_, red_neg ϖ k h0⟩
  show cT σ (-h0) = -h0
  have hh' : cT σ h0 = h0 := hh
  ext i j
  have e : σ (h0 j i) = h0 i j := congrFun (congrFun hh' i) j
  show σ (-(h0 j i)) = -(h0 i j)
  rw [map_neg, e]
end GlobalTheory.CompanionTheory.SiegLoc.LevelId
