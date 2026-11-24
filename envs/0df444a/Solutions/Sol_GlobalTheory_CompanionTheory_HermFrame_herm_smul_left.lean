-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermFrame.herm_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:38:14.213029+00:00
-- url     : https://prove2.me/submissions/482dee0d-7491-4c8f-b110-5c993e05bce4

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
theorem _root_.solution (hh : IsHerm s h) (a : L) (x y : V) : h (a • x) y = s a * h x y := by
  obtain ⟨_, h2, h3, _⟩ := hh
  rw [h3 y (a • x), h2, map_mul, ← h3 y x]
end GlobalTheory.CompanionTheory.HermFrame
