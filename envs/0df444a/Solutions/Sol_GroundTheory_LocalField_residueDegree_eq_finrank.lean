-- Prove2me | solution 1 for GroundTheory.LocalField.residueDegree_eq_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:27.687539+00:00
-- url     : https://prove2.me/submissions/5cdf7caf-6105-49be-811c-bdece5303957

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Integers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]
variable [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution : residueDegree K L = Module.finrank 𝓀[K] 𝓀[L] :=
  Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal 𝒪[K]) (IsLocalRing.maximalIdeal 𝒪[L])
end GroundTheory.LocalField
