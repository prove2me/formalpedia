-- Prove2me | solution 1 for GroundTheory.LocalField.modulus_add_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:42:31.76221+00:00
-- url     : https://prove2.me/submissions/946c9f48-9add-472d-93d0-d00060bd7053

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
import Theorems.Thm_GroundTheory_LocalField_modulus_of_ne_zero
import Theorems.Thm_GroundTheory_LocalField_ord_add_eq

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
open ValuativeRel MeasureTheory Measure Topology Filter TopologicalSpace
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace GroundTheory.LocalField
theorem _root_.solution {x d : K} (hx : x ≠ 0) (hd : d ∈ valBall K (ord x + 1)) :
    modulus (x + d) = modulus x := by
  obtain ⟨h1, h2⟩ := ord_add_eq hx hd
  rw [modulus_of_ne_zero h1, modulus_of_ne_zero hx, h2]
end GroundTheory.LocalField
