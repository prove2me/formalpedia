-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.HermSp.zero_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:35:16.565307+00:00
-- url     : https://prove2.me/submissions/ac9aff84-af0f-46f4-9211-0e093713840a

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
theorem _root_.solution (v : V) : B.h v 0 = 0 := by
  rw [B.symm 0 v, B.zero_left, map_zero]
end GlobalTheory.CompanionTheory.UnrDens.HermSp
