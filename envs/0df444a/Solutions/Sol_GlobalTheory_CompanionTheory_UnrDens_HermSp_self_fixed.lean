-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.HermSp.self_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:51:48.980497+00:00
-- url     : https://prove2.me/submissions/7885bedc-76e9-4725-bbd0-75a47a714385

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
theorem _root_.solution (hτ : ∀ a, τ (τ a) = a) (v : V) : τ (B.h v v) = B.h v v := by
  exact (B.symm v v).symm
end GlobalTheory.CompanionTheory.UnrDens.HermSp
