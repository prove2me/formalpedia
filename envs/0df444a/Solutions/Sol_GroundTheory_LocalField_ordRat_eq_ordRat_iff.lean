-- Prove2me | solution 1 for GroundTheory.LocalField.ordRat_eq_ordRat_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:13.391213+00:00
-- url     : https://prove2.me/submissions/fd4b0d09-ef18-4160-ae36-7a3bb2072809

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
import Theorems.Thm_GroundTheory_LocalField_ordRat_le_ordRat_iff

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
open ValuativeRel IsLocalRing
open scoped WithZero
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [Algebra K Ω] [ValuativeExtension K Ω]
variable {K}
variable [Algebra.IsAlgebraic K Ω]
namespace GroundTheory.LocalField
theorem _root_.solution {x y : Ω} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordRat K x = ordRat K y ↔ valuation Ω x = valuation Ω y := by
  rw [le_antisymm_iff, le_antisymm_iff, ordRat_le_ordRat_iff hx hy, ordRat_le_ordRat_iff hy hx,
    and_comm]
end GroundTheory.LocalField
