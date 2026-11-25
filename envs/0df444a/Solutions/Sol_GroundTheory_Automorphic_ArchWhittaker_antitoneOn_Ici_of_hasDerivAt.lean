-- Prove2me | solution 1 for GroundTheory.Automorphic.ArchWhittaker.antitoneOn_Ici_of_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:47:58.70488+00:00
-- url     : https://prove2.me/submissions/84d5066b-0ebf-44db-9fb8-ad075c489944

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_WronskianEqZeroOfModerate
import Theorems.Thm_GroundTheory_Automorphic_ArchWhittaker_monotoneOn_Ici_of_hasDerivAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ArchWhittaker
open Filter Topology Set
namespace GroundTheory.Automorphic.ArchWhittaker
theorem _root_.solution {u u' : ℝ → ℝ} {a : ℝ}
    (hu : ∀ y ≥ a, HasDerivAt u (u' y) y) (hneg : ∀ y ≥ a, u' y ≤ 0) : AntitoneOn u (Ici a) := by
  have := monotoneOn_Ici_of_hasDerivAt (u := fun y => -u y) (u' := fun y => -u' y)
    (fun y hy => (hu y hy).neg) (fun y hy => neg_nonneg.2 (hneg y hy))
  intro x hx y hy hxy
  have := this hx hy hxy
  simpa using this
end GroundTheory.Automorphic.ArchWhittaker
