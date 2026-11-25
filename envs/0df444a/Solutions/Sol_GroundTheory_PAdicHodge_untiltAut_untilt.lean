-- Prove2me | solution 1 for GroundTheory.PAdicHodge.untiltAut_untilt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:05:29.703092+00:00
-- url     : https://prove2.me/submissions/26044098-e42a-476a-86e0-030336fb0cf3

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltPerfectoid
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGalois
import Theorems.Thm_GroundTheory_PAdicHodge_untiltAut_coe

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
theorem _root_.solution (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] (σ : N ≃ₐ[K♭] N)
    (b : PreTilt (normInteger (untiltField K C p N)) p) :
    untiltAut N σ ((PreTilt.untilt b : normInteger (untiltField K C p N)) : untiltField K C p N) =
      ((PreTilt.untilt (untiltPreTiltAut N σ b) : normInteger (untiltField K C p N)) :
        untiltField K C p N) := by
  rw [untiltAut_coe, ← WittVector.fontaineTheta_teichmuller, untiltIntegerHom_fontaineTheta,
    WittVector.map_teichmuller, WittVector.fontaineTheta_teichmuller]
end GroundTheory.PAdicHodge
