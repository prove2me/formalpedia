-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermPlane.herm_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:23.463559+00:00
-- url     : https://prove2.me/submissions/12cf92c2-8988-4f4d-813a-2213d8adfabc

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PlaneOfHenselAndPairing
import Theorems.Thm_GlobalTheory_CompanionTheory_HermPlane_herm_add_left
import Theorems.Thm_GlobalTheory_CompanionTheory_HermPlane_herm_smul_left

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermPlane
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {V : Type} [AddCommGroup V] [Module L V]
namespace GlobalTheory.CompanionTheory.HermPlane
theorem _root_.solution {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) (a c : L) (x y : V) :
    h (c • x + a • y) (c • x + a • y) =
      s c * (c * h x x) + s c * (a * h x y) + s a * (c * h y x) + s a * (a * h y y) := by
  rw [herm_add_left hh, hh.1, hh.1, herm_smul_left hh, herm_smul_left hh, hh.2.1, hh.2.1,
    herm_smul_left hh, herm_smul_left hh, hh.2.1, hh.2.1]
  ring
end GlobalTheory.CompanionTheory.HermPlane
