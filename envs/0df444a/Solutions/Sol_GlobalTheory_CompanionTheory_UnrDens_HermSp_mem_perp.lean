-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.HermSp.mem_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:35:11.651136+00:00
-- url     : https://prove2.me/submissions/878fbea3-4335-4321-97a2-4ca684d4ed41

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens
variable {E : Type} [CommRing E] {τ : E →+* E}
variable {V : Type} [AddCommGroup V] [Module E V]
open GlobalTheory.CompanionTheory.UnrDens.HermSp
variable (B : HermSp E τ V)
namespace GlobalTheory.CompanionTheory.UnrDens.HermSp
theorem _root_.solution {w v : V} : v ∈ B.perp w ↔ B.h v w = 0 := by
  exact Iff.rfl
end GlobalTheory.CompanionTheory.UnrDens.HermSp
