-- Prove2me | solution 1 for GroundTheory.PAdicHodge.tiltMap_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:30:52.99778+00:00
-- url     : https://prove2.me/submissions/4b687796-49fc-4cc7-a402-51c4747cedc8

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_TiltField
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_TiltMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable {K L : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField L] [IsUltrametricDist L]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField L p]
variable (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖)
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪L♭" => PreTilt (normInteger L) p
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "L♭" => Tilt L NormedField.valuation (normInteger L) normInteger_integers p
namespace GroundTheory.PAdicHodge
theorem _root_.solution (a : 𝒪K♭) :
    tiltMap p φ hφ (algebraMap 𝒪K♭ K♭ a) = algebraMap 𝒪L♭ L♭ (preTiltMap p φ hφ a) :=
  IsLocalization.map_eq (M := nonZeroDivisors 𝒪K♭) (S := K♭) (T := nonZeroDivisors 𝒪L♭)
    (Q := L♭)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (preTiltMap_injective φ hφ)) a
end GroundTheory.PAdicHodge
