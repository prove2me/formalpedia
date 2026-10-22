-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmicDegreeBound_add_support_v2
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-21T16:49:12.06006+00:00
-- url     : https://prove2.me/submissions/3c2a9279-eeb9-4530-aa3b-8c98540cf00c

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (w : Fin d → Rat) (N : Real)
    (F G : MvPolynomial (Fin d) Complex)
    (hF : logarithmicDegreeBound w N F)
    (hG : logarithmicDegreeBound w N G) :
    logarithmicDegreeBound w N (F + G) := by
  classical
  intro a ha
  have hmem : a ∈ F.support ∪ G.support := MvPolynomial.support_add ha
  rcases Finset.mem_union.mp hmem with h | h
  · exact hF a h
  · exact hG a h
