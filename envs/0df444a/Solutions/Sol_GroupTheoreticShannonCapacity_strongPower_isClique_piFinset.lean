-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.strongPower_isClique_piFinset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:36:46.107048+00:00
-- url     : https://prove2.me/submissions/87cbea47-f2ed-42b1-b5cd-9da6573b78f0

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Basic

set_option autoImplicit true
open GroupTheoreticShannonCapacity
namespace GroupTheoreticShannonCapacity
theorem _root_.solution (G : SimpleGraph V) (n : ℕ)
    (sets : Fin n → Finset V) (hclique : ∀ i, G.IsClique (sets i)) :
    (strongPower G n).IsClique (Fintype.piFinset sets) := by
  classical
  rw [SimpleGraph.isClique_iff]
  intro f hf g hg hfg
  have hf' := Fintype.mem_piFinset.mp hf
  have hg' := Fintype.mem_piFinset.mp hg
  simp only [strongPower]
  constructor
  · exact hfg
  · intro i
    by_cases heq : f i = g i
    · left; exact heq
    · right
      have hclique_i := hclique i
      rw [SimpleGraph.isClique_iff] at hclique_i
      exact hclique_i (hf' i) (hg' i) heq
end GroupTheoreticShannonCapacity
