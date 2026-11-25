-- Prove2me | solution 1 for GroundTheory.LocalField.EqualChar.powerSeriesHom_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:37:53.317623+00:00
-- url     : https://prove2.me/submissions/188d9598-ca60-4f6e-9061-426ae1544e2d

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Examples
import Definitions.Def_GroundTheory_LocalFields_ExamplesTeichmuller
import Definitions.Def_GroundTheory_LocalFields_ExamplesLaurent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open scoped LaurentSeries
open GroundTheory GroundTheory.LocalField
open ValuativeRel Polynomial IsLocalRing Topology Filter WithZero HahnSeries
open GroundTheory.LocalField.EqualChar
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (p : ℕ) [Fact p.Prime] [CharP K p]
attribute [local instance] GroundTheory.LocalField.EqualChar.uniformSpaceK
attribute [local instance] GroundTheory.LocalField.EqualChar.isUniformAddGroupK
attribute [local instance] GroundTheory.LocalField.EqualChar.uniformSpaceResidue
attribute [local instance] GroundTheory.LocalField.EqualChar.discreteUniformityResidue
namespace GroundTheory.LocalField.EqualChar
theorem _root_.solution (a : 𝓀[K]) :
    powerSeriesHom K p (PowerSeries.C a) = teichmullerHom K p a := by
  rw [powerSeriesHom_apply, PowerSeries.eval₂_C]
end GroundTheory.LocalField.EqualChar
