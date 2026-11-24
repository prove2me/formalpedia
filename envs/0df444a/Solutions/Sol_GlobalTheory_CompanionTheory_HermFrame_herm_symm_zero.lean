-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermFrame.herm_symm_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:38:15.144891+00:00
-- url     : https://prove2.me/submissions/ef2f4ff3-b84f-4b03-8eeb-6dc98777c4bb

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FrameOfAnisotropicPlaneSplitting

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermFrame
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L}
namespace GlobalTheory.CompanionTheory.HermFrame
theorem _root_.solution (hh : IsHerm s h) {x y : V} (hxy : h x y = 0) : h y x = 0 := by
  rw [hh.2.2.1 x y, hxy, map_zero]
end GlobalTheory.CompanionTheory.HermFrame
