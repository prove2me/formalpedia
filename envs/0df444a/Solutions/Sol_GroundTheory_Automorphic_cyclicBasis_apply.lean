-- Prove2me | solution 1 for GroundTheory.Automorphic.cyclicBasis_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:49.484676+00:00
-- url     : https://prove2.me/submissions/e04f60f6-9ace-48c9-88f3-eb43bf7a3096

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjCyclic

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
theorem _root_.solution (hv : IsCyclicVector f v) (k : Fin (finrank E V)) :
    cyclicBasis hv k = (f ^ (k : ℕ)) v :=
  congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' (K := E) _ hv _) k
end GroundTheory.Automorphic
