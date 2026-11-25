-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_eq_of_norm_sub_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:19:04.930638+00:00
-- url     : https://prove2.me/submissions/7b77e07b-e47a-4dd1-83bc-486a59da525f

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
omit [NontriviallyNormedField K] [IsUltrametricDist K] [NontriviallyNormedField C] [NormedAlgebra K C]
  [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {E : Type*} [SeminormedAddCommGroup E] [IsUltrametricDist E]
    {x y : E} (h : ‖x - y‖ < ‖y‖) : ‖x‖ = ‖y‖ := by
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne
  rw [sub_add_cancel, max_eq_right h.le] at this
  exact this
end GroundTheory.PAdicHodge
