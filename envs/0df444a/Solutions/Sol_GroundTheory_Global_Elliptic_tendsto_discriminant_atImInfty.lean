-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.tendsto_discriminant_atImInfty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:59:09.316133+00:00
-- url     : https://prove2.me/submissions/92b6aed9-998c-47fc-adc9-23b87231098b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_JInvariant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_JInvariantSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex UpperHalfPlane ModularForm EisensteinSeries MatrixGroups Filter Topology Set
open scoped PeriodPair Real Modular
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
namespace GroundTheory.Global.Elliptic
theorem _root_.solution :
    Tendsto (fun τ : ℍ ↦ ModularForm.discriminant τ) atImInfty (𝓝 0) :=
  ModularForm.discriminant_isZeroAtImInfty
end GroundTheory.Global.Elliptic
