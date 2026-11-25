-- Prove2me | solution 1 for GroundTheory.LocalField.evalQpow_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:08:27.622706+00:00
-- url     : https://prove2.me/submissions/15cb171f-6eaf-466b-b2ec-0475b308ab63

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaChar
import Definitions.Def_GroundTheory_LocalFields_LocalZetaIntegral

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
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace GroundTheory.LocalField
theorem _root_.solution {ι : Type*} (t : Finset ι) (P : ι → LaurentPolynomial ℂ) (s : ℂ) :
    evalQpow K (∑ i ∈ t, P i) s = ∑ i ∈ t, evalQpow K (P i) s := map_sum _ _ _
end GroundTheory.LocalField
