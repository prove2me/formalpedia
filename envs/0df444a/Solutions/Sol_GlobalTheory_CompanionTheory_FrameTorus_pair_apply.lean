-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FrameTorus.pair_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:56:38.093792+00:00
-- url     : https://prove2.me/submissions/63ab7ece-dcb6-4ac9-9696-4f2eb1fc820b

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TorusStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FrameTorus
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
namespace GlobalTheory.CompanionTheory.FrameTorus
theorem _root_.solution {s : L →+* L} {h : V → V → L} (hH : IsHerm s h) (x y : V) :
    pair hH x y = h x y := rfl
end GlobalTheory.CompanionTheory.FrameTorus
