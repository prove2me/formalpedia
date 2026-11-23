-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.independenceNumber_ge_card_of_independent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:36:49.929502+00:00
-- url     : https://prove2.me/submissions/9518480a-2d55-44c4-a3d0-35908b940e4a

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Basic

set_option autoImplicit true
open GroupTheoreticShannonCapacity
namespace GroupTheoreticShannonCapacity
theorem _root_.solution (G : SimpleGraph V) [Fintype V]
    (S : Finset V) (hS : G.IsIndepSet (S : Set V)) :
    G.indepNum ≥ S.card := by
  simpa using
    (SimpleGraph.IsIndepSet.card_le_indepNum (G := G) (t := S) hS)
end GroupTheoreticShannonCapacity
