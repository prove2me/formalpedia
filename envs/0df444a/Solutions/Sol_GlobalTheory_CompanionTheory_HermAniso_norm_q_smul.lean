-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermAniso.norm_q_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:03:50.189336+00:00
-- url     : https://prove2.me/submissions/7db9827f-16c3-4350-b389-62b728812380

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AnisotropicOfHenselAndSandwich
import Theorems.Thm_GlobalTheory_CompanionTheory_HermAniso_smul_left

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermAniso
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L}
namespace GlobalTheory.CompanionTheory.HermAniso
theorem _root_.solution (hs : IsInv s) (hh : IsHerm s h) (a : L) (x : V) :
    ‖h (a • x) (a • x)‖ = ‖a‖ * ‖a‖ * ‖h x x‖ := by
  rw [smul_left hh, hh.2.1, norm_mul, norm_mul, hs.2.1]; ring
end GlobalTheory.CompanionTheory.HermAniso
