-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.independenceNumber_le_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:36:55.848333+00:00
-- url     : https://prove2.me/submissions/6eeeadab-8c18-433e-8bb5-0a77333d538a

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Basic

set_option autoImplicit true
open GroupTheoreticShannonCapacity
namespace GroupTheoreticShannonCapacity
theorem _root_.solution (G : SimpleGraph V) [Fintype V] :
    G.indepNum ≤ Fintype.card V := by
  classical
  obtain ⟨S, hSmax⟩ := SimpleGraph.maximumIndepSet_exists (G := G)
  have hS_card : S.card = G.indepNum := by
    simpa using
      (SimpleGraph.maximumIndepSet_card_eq_indepNum (G := G) S hSmax)
  have hle : S.card ≤ Fintype.card V := by
    simpa using (Finset.card_le_univ (s := S))
  simpa [hS_card] using hle
end GroupTheoreticShannonCapacity
