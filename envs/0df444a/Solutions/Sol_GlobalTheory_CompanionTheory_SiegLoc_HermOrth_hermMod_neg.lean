-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegLoc.HermOrth.hermMod_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:38:12.38295+00:00
-- url     : https://prove2.me/submissions/1b85007e-b3a7-48ed-831a-5740ee8c14ef

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCharacterOrthogonality
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SiegLoc_HermOrth_red_neg__9b7cf759e7aa
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SiegLoc_HermOrth_cT_neg__c113ada7890a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegLoc GlobalTheory.CompanionTheory.SiegLoc.HermOrth
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.SiegLoc.HermOrth
theorem _root_.solution {σ : R →+* R} {ϖ : R} {n k : ℕ}
    (a : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) (ha : a ∈ hermMod σ ϖ n k) :
    -a ∈ hermMod σ ϖ n k := by
  unfold PositivityTheory.PfSWUS.Loc.hermMod at ha ⊢
  obtain ⟨a', ha', rfl⟩ := ha
  have ha'' : PositivityTheory.PfSWUS.Loc.cT σ a' = a' := ha'
  refine ⟨-a', ?_, GlobalTheory.CompanionTheory.SiegLoc.HermOrth.red_neg' _ _ _⟩
  show PositivityTheory.PfSWUS.Loc.cT σ (-a') = -a'
  rw [GlobalTheory.CompanionTheory.SiegLoc.HermOrth.cT_neg', ha'']
end GlobalTheory.CompanionTheory.SiegLoc.HermOrth
