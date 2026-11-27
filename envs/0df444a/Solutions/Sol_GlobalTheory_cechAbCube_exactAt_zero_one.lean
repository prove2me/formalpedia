-- Prove2me | solution 1 for GlobalTheory.cechAbCube_exactAt_zero_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:36:07.261447+00:00
-- url     : https://prove2.me/submissions/c23ab90e-db83-4dc6-8b22-8af63160182a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoCechComplexMapPresheafCubeRes
import Theorems.Thm_GlobalTheory_presheafCube_exactAt_zero_one

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
    (hc : V ≤ ⨆ i, U i) :
    (cubeComplex (cechAbCube P V U)).ExactAt 0 ∧ (cubeComplex (cechAbCube P V U)).ExactAt 1 :=
  presheafCube_exactAt_zero_one (isSheaf_comp_abToIntModule hP) hc
end GlobalTheory
