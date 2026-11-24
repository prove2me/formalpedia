-- Prove2me | solution 1 for GlobalTheory.isIso_cechAugHomology_presheafCube
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:03:35.654919+00:00
-- url     : https://prove2.me/submissions/b0b85b93-091e-43f4-b441-35f07956a246

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoCechComplexMapPresheafCubeRes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace Opposite
universe w v u
noncomputable section
open GlobalTheory
variable {T : TopCat.{w}} {ι : Type} {R : Type u} [Ring R]
  {P : (Opens T)ᵒᵖ ⥤ ModuleCat.{w} R} (hP : Presheaf.IsSheaf (Opens.grothendieckTopology T) P)
  {V : Opens T} {U : ι → Opens T} (hc : V ≤ ⨆ i, U i)
include hP hc
variable [LinearOrder ι]
namespace GlobalTheory
theorem _root_.solution : IsIso (cechAugHomology (presheafCube P V U)) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact (Function.Bijective.of_comp_iff _ (presheafCubeEmptyEquiv P V U).bijective).1
    (presheafToCechH_bijective hP hc)
end GlobalTheory
