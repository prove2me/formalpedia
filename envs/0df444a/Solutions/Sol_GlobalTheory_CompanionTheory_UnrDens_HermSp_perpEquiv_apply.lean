-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.HermSp.perpEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:52:04.769051+00:00
-- url     : https://prove2.me/submissions/63406bca-0623-4833-922c-d87993af0917

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
theorem _root_.solution {w : V} (hw : IsUnit (B.h w w)) (p : E × B.perp w) :
    B.perpEquiv hw p = p.1 • w + (p.2 : V) := rfl
end GlobalTheory.CompanionTheory.UnrDens.HermSp
