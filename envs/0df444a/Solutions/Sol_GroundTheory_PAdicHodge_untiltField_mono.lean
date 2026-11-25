-- Prove2me | solution 1 for GroundTheory.PAdicHodge.untiltField_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:30:49.743699+00:00
-- url     : https://prove2.me/submissions/1f1d5d61-a814-4bb7-bda5-ca3d40ca7053

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_UntiltField
import Theorems.Thm_GroundTheory_PAdicHodge_untiltInteger_mono

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
local notation "𝒪C♭" => PreTilt (normInteger C) p
local notation "θ" => WittVector.fontaineTheta (normInteger C) p
namespace GroundTheory.PAdicHodge
theorem _root_.solution {N N' : IntermediateField K♭ C♭} (h : N ≤ N') :
    untiltField K C p N ≤ untiltField K C p N' :=
  IntermediateField.adjoin.mono _ _ _ (Set.image_mono (untiltInteger_mono h))
end GroundTheory.PAdicHodge
