-- Prove2me | solution 1 for GroundTheory.Automorphic.exists_isCyclicVector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:34:21.872838+00:00
-- url     : https://prove2.me/submissions/2a97f4d6-bf8f-4663-89cf-25fd0ded4679

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjCyclic
import Theorems.Thm_GroundTheory_Automorphic_exists_linearIndependent_pow_apply

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
namespace GroundTheory.Automorphic
theorem _root_.solution [Infinite E] (f : Module.End E V) (hf : f.charpoly.Separable) :
    ∃ v, IsCyclicVector f v :=
  exists_linearIndependent_pow_apply f hf
end GroundTheory.Automorphic
