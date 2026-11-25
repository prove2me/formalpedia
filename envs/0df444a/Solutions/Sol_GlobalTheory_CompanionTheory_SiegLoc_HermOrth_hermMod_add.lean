-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegLoc.HermOrth.hermMod_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:38:10.226426+00:00
-- url     : https://prove2.me/submissions/e66ced17-5c75-48a7-a89c-00d7cfd85d72

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCharacterOrthogonality
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SiegLoc_HermOrth_red_add__ae89ccb36cf7
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SiegLoc_HermOrth_cT_add__abfcc11f156d

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
    (a b : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) (ha : a ∈ hermMod σ ϖ n k)
    (hb : b ∈ hermMod σ ϖ n k) : a + b ∈ hermMod σ ϖ n k := by
  unfold PositivityTheory.PfSWUS.Loc.hermMod at ha hb ⊢
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  have ha'' : PositivityTheory.PfSWUS.Loc.cT σ a' = a' := ha'
  have hb'' : PositivityTheory.PfSWUS.Loc.cT σ b' = b' := hb'
  refine ⟨a' + b', ?_, GlobalTheory.CompanionTheory.SiegLoc.HermOrth.red_add' _ _ _ _⟩
  show PositivityTheory.PfSWUS.Loc.cT σ (a' + b') = a' + b'
  rw [GlobalTheory.CompanionTheory.SiegLoc.HermOrth.cT_add', ha'', hb'']
end GlobalTheory.CompanionTheory.SiegLoc.HermOrth
