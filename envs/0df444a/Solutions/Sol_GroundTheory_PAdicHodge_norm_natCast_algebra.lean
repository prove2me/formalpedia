-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_natCast_algebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:08:23.522435+00:00
-- url     : https://prove2.me/submissions/4ff280e7-9ab4-4f81-9e2a-b8f0746918a8

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_OrthoBasis
import Definitions.Def_GroundTheory_PAdicHodge_UntiltIndep

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
omit [IsUltrametricDist K] [IsUltrametricDist C] [Fact p.Prime] [IsPerfectoidField K p]
  [IsPerfectoidField C p]
namespace GroundTheory.PAdicHodge
theorem _root_.solution : ‖(p : C)‖ = ‖(p : K)‖ := by
  rw [← map_natCast (algebraMap K C), norm_algebraMap']
end GroundTheory.PAdicHodge
