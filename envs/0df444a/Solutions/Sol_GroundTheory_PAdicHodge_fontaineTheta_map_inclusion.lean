-- Prove2me | solution 1 for GroundTheory.PAdicHodge.fontaineTheta_map_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:52:34.470023+00:00
-- url     : https://prove2.me/submissions/d30265d0-a01c-4737-81d1-5bfd555313a0

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltEquiv
import Definitions.Def_GroundTheory_PAdicHodge_FWNatural
import Theorems.Thm_GroundTheory_PAdicHodge_integerTilt_mono


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
theorem _root_.solution {N N' : IntermediateField K♭ C♭} (h : N ≤ N')
    (u : WittVector p (integerTilt K C p N)) :
    θ (WittVector.map (integerTilt K C p N').subtype
        (WittVector.map (Subring.inclusion (integerTilt_mono h)) u)) =
      θ (WittVector.map (integerTilt K C p N).subtype u) := by
  rw [← wittVector_map_comp]
  rfl
end GroundTheory.PAdicHodge
