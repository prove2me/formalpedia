-- Prove2me | solution 1 for GroundTheory.LocalField.finiteIndex_of_isOpen_integerUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:04:38.408226+00:00
-- url     : https://prove2.me/submissions/4fb88ef6-72e0-4e0c-8f6c-366206c4e263

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocalBase
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivialLocal
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocal

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
open ValuativeRel GroundTheory.GroupCoh GroundTheory.Global
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Algebra K L]
  [ValuativeExtension K L] [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution {V : Subgroup 𝒪[L]ˣ} (h : IsOpen (V : Set 𝒪[L]ˣ)) :
    V.FiniteIndex := by
  have : Finite (𝒪[L]ˣ ⧸ V) := Subgroup.quotient_finite_of_isOpen V h
  exact Subgroup.finiteIndex_of_finite_quotient
end GroundTheory.LocalField
