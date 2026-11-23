-- Prove2me | solution 1 for GroundTheory.LocalField.ramificationIndex_mul_residueDegree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:34.944064+00:00
-- url     : https://prove2.me/submissions/b9e4dbc5-a910-415b-b451-ab6874dc0db5

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Integers
import Theorems.Thm_GroundTheory_LocalField_finrank_integer

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
theorem _root_.solution :
    ramificationIndex K L * residueDegree K L = Module.finrank K L := by
  let : Fintype ((IsLocalRing.maximalIdeal 𝒪[K]).primesOver 𝒪[L]) := Fintype.ofFinite _
  have := Ideal.sum_ramification_inertia_eq_finrank (IsLocalRing.maximalIdeal 𝒪[K]) 𝒪[L]
  rw [Fintype.sum_unique, finrank_integer] at this
  exact this
end GroundTheory.LocalField
