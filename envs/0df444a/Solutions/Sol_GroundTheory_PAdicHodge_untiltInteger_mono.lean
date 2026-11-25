-- Prove2me | solution 1 for GroundTheory.PAdicHodge.untiltInteger_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:23:22.243071+00:00
-- url     : https://prove2.me/submissions/b4807d84-3e45-442c-945d-b239ba2dfa12

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_UntiltField
import Theorems.Thm_GroundTheory_PAdicHodge_integerTilt_mono
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.tiltMap_algebraMap



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
    untiltInteger K C p N ≤ untiltInteger K C p N' := by
  rintro _ ⟨u, rfl⟩
  refine ⟨WittVector.map (Subring.inclusion (integerTilt_mono h)) u, ?_⟩
  simp only [RingHom.comp_apply]
  congr 1
end GroundTheory.PAdicHodge
