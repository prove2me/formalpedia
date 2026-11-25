-- Prove2me | solution 1 for GroundTheory.Automorphic.IsCyclicVector.commute_of_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:18:13.211459+00:00
-- url     : https://prove2.me/submissions/eb79fc6b-7e47-4ef8-a392-f522d6a4c495

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjCyclic
import Theorems.Thm_GroundTheory_Automorphic_IsCyclicVector_exists_eq_aeval

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
namespace IsCyclicVector
theorem _root_.solution (hv : IsCyclicVector f v) {g g' : Module.End E V}
    (hg : Commute f g) (hg' : Commute f g') : Commute g g' := by
  obtain ⟨p, rfl⟩ := hv.exists_eq_aeval hg
  obtain ⟨q, rfl⟩ := hv.exists_eq_aeval hg'
  exact (Commute.all p q).map (aeval f)
end IsCyclicVector
end GroundTheory.Automorphic
