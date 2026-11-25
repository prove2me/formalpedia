-- Prove2me | solution 1 for GroundTheory.PAdicHodge.finiteDimensional_of_le_tilt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:58:05.196732+00:00
-- url     : https://prove2.me/submissions/675c2173-7efb-4b8e-9bc0-e04323d3d18f

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltEquiv
import Definitions.Def_GroundTheory_PAdicHodge_FWNatural

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
theorem _root_.solution {M N : IntermediateField K♭ C♭} [FiniteDimensional K♭ N]
    (h : M ≤ N) : FiniteDimensional K♭ M :=
  Module.Finite.of_injective (IntermediateField.inclusion h).toLinearMap
    (IntermediateField.inclusion h).injective
end GroundTheory.PAdicHodge
