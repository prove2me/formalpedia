-- Prove2me | solution 1 for GlobalTheory.presheafCube_exactAt_zero_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:12:45.273651+00:00
-- url     : https://prove2.me/submissions/c52fc38e-0fb4-4faa-914c-67879ee42501

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoCechComplexMapPresheafCubeRes
import Theorems.Thm_GlobalTheory_isIso_cechAugHomology_presheafCube
import Theorems.Thm_GlobalTheory_isIso_cechAugHomology_iff


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
theorem _root_.solution :
    (cubeComplex (presheafCube P V U)).ExactAt 0 ∧ (cubeComplex (presheafCube P V U)).ExactAt 1 :=
  (isIso_cechAugHomology_iff _).1 (isIso_cechAugHomology_presheafCube hP hc)
end GlobalTheory
