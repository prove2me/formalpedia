-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.mem_polyLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:19:52.279603+00:00
-- url     : https://prove2.me/submissions/47bcd5bf-eb18-4dd3-8a0b-ee5b5485314d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_LeadingTerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution {d : ℕ} {p : MvPolynomial (Fin n) ℂ} : p ∈ polyLE n d ↔ p.totalDegree ≤ d := by
  rw [polyLE, mem_restrictTotalDegree]
end GroundTheory.Automorphic.HarishChandra
