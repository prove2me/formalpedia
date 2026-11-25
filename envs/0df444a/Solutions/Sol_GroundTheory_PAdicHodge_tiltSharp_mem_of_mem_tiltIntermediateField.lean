-- Prove2me | solution 1 for GroundTheory.PAdicHodge.tiltSharp_mem_of_mem_tiltIntermediateField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:23:17.220811+00:00
-- url     : https://prove2.me/submissions/49e03516-0d4f-41cd-b015-f45ab027926c

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_TiltField
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_TiltMap
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Theorems.Thm_GroundTheory_PAdicHodge_tiltSharp_tiltMap


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
variable (F : IntermediateField K C) [IsPerfectoidField F p]
local notation "F♭" => Tilt F NormedField.valuation (normInteger F) normInteger_integers p
namespace GroundTheory.PAdicHodge
theorem _root_.solution {z : C♭}
    (hz : z ∈ tiltIntermediateField p F) : tiltSharp C p z ∈ F := by
  obtain ⟨y, rfl⟩ := hz
  rw [tiltInclusion, tiltSharp_tiltMap]
  exact (tiltSharp F p y).2
end GroundTheory.PAdicHodge
