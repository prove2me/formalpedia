-- Prove2me | solution 1 for GroundTheory.LocalField.EqualChar.residue_teichmullerHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:10:51.368323+00:00
-- url     : https://prove2.me/submissions/21dc7127-eb2a-446b-bbce-f54c59653599

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_ExamplesTeichmuller

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel Polynomial IsLocalRing
open GroundTheory.LocalField.EqualChar
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (p : ℕ) [hp : Fact p.Prime] [CharP K p]
namespace GroundTheory.LocalField.EqualChar
theorem _root_.solution (a : 𝓀[K]) : residue 𝒪[K] (teichmullerHom K p a) = a :=
  (teichmullerEquiv K p).apply_symm_apply a
end GroundTheory.LocalField.EqualChar
