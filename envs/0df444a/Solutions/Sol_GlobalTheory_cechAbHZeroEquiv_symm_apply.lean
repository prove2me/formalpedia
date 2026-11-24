-- Prove2me | solution 1 for GlobalTheory.cechAbHZeroEquiv_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:54:25.612496+00:00
-- url     : https://prove2.me/submissions/e7add0e8-e5f6-4f98-a0c9-c585b989f832

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
variable {T : TopCat.{w}} {ι : Type} {P Q : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{w}}
  {V : Opens T} {U : ι → Opens T}
variable [LinearOrder ι]
namespace GlobalTheory
theorem _root_.solution (hP : Presheaf.IsSheaf (Opens.grothendieckTopology T) P)
    (hc : V ≤ ⨆ i, U i) (x : P.obj (op V)) :
    (cechAbHZeroEquiv hP hc).symm x = toCechAbH P V U x := rfl
end GlobalTheory
