-- Prove2me | solution 1 for GroundTheory.PAdicHodge.untiltPreTiltMap_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:35:30.262815+00:00
-- url     : https://prove2.me/submissions/305f579b-5e46-4657-a002-665ade6b5523

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGalois
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGaloisCorr

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
variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪C♭" => PreTilt (normInteger C) p
namespace GroundTheory.PAdicHodge
theorem _root_.solution (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (a : integerTilt K C p N) :
    untiltPreTiltMap N ((preTiltUntiltEquiv N).symm a) = a := by
  rw [← coe_preTiltUntiltEquiv, RingEquiv.apply_symm_apply]
end GroundTheory.PAdicHodge
