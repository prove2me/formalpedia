-- Prove2me | solution 1 for GroundTheory.PAdicHodge.isPerfectoidField_of_isAlgClosed_of_normedAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:00:09.832777+00:00
-- url     : https://prove2.me/submissions/4a61b505-c970-4d94-bfc1-71ede72beb3f

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltPerfectoid
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApprox
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGalois
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGaloisCorr
import Definitions.Def_GroundTheory_PAdicHodge_CompletedAlgClosure
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidCharP
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidCriterion
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgClosed
import Definitions.Def_GroundTheory_PAdicHodge_TiltEquiv

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
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C] [IsAlgClosed C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
variable (K C p)
include K
namespace GroundTheory.PAdicHodge
theorem _root_.solution [CompleteSpace C] :
    IsPerfectoidField C p :=
  IsPerfectoidField.of_isAlgClosed p (by
    rw [← map_natCast (algebraMap K C), norm_algebraMap']
    exact IsPerfectoidField.norm_natCast_lt_one)
end GroundTheory.PAdicHodge
