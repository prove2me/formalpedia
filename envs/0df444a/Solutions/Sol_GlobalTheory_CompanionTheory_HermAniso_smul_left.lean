-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermAniso.smul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:12.826917+00:00
-- url     : https://prove2.me/submissions/8b46e2e4-18ac-414e-b08c-68a2d52e1eed

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AnisotropicOfHenselAndSandwich

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
theorem _root_.solution (hh : IsHerm s h) (a : L) (x y : V) : h (a • x) y = s a * h x y := by
  have h1 := hh.2.2.1
  rw [h1 y (a • x), hh.2.1, map_mul, h1 y x]
end GlobalTheory.CompanionTheory.HermAniso
