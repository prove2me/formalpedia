-- Prove2me | solution 1 for GroundTheory.LocalField.adicCompletionRingEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:48:40.735152+00:00
-- url     : https://prove2.me/submissions/76ef51ea-d1a3-4d5d-bead-e7c18a5444ca

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramifiedIntegers
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_UnitMulPowAdic
import Definitions.Def_GroundTheory_LocalFields_CompletedUnramified

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
open IsLocalRing ValuativeRel
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
local notation "𝔅" => AdicCompletion (maximalIdeal R) R
namespace GroundTheory.LocalField
theorem _root_.solution (θ : R ≃+* R) (x : 𝔅) :
    adicCompletionRingEquiv θ x =
      adicCompletionMap (θ : R →+* R) (maximalIdeal_le_comap_ringEquiv θ) x :=
  rfl
end GroundTheory.LocalField
