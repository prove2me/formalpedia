-- Prove2me | solution 1 for GroundTheory.Automorphic.commute_of_commute_of_separable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:40:59.330082+00:00
-- url     : https://prove2.me/submissions/5505666d-4c15-48a0-8fa8-ba4c169be5f5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjCyclic
import Theorems.Thm_GroundTheory_Automorphic_exists_isCyclicVector
import Theorems.Thm_GroundTheory_Automorphic_IsCyclicVector_commute_of_commute

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Polynomial Module Matrix
variable {E V V' : Type*} [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  [AddCommGroup V'] [Module E V'] [FiniteDimensional E V']
variable {f : Module.End E V} {v : V}
namespace GroundTheory.Automorphic
theorem _root_.solution [Infinite E] {f g g' : Module.End E V}
    (hf : f.charpoly.Separable) (hg : Commute f g) (hg' : Commute f g') : Commute g g' := by
  obtain ⟨v, hv⟩ := exists_isCyclicVector f hf
  exact hv.commute_of_commute hg hg'
end GroundTheory.Automorphic
