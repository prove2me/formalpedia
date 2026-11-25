-- Prove2me | solution 1 for GroundTheory.LocalField.orderOf_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:43:40.874178+00:00
-- url     : https://prove2.me/submissions/9c183b6a-aa10-4d1e-bf97-f57f3aae444e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
import Theorems.Thm_GroundTheory_LocalField_residueDegree_eq_finrank


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
open ValuativeRel Polynomial IntermediateField
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable (K L)
namespace GroundTheory.LocalField
theorem _root_.solution (h : ramificationIndex K L = 1) :
    orderOf (frobenius K L h) = Module.finrank K L := by
  let := Fintype.ofFinite 𝓀[K]
  rw [frobenius, MulEquiv.orderOf_eq, FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic,
    ← residueDegree_eq_finrank, residueDegree_eq_finrank_of_unramified K L h]
end GroundTheory.LocalField
