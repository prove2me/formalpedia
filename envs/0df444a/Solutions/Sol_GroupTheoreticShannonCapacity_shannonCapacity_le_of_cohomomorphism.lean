-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.shannonCapacity_le_of_cohomomorphism
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:39:04.600031+00:00
-- url     : https://prove2.me/submissions/b0d6fb76-cfd8-4fee-95ad-36cfd1458109

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Theorems.Thm_GroupTheoreticShannonCapacity_independenceNumber_le_of_cohomomorphism
import Theorems.Thm_GroupTheoreticShannonCapacity_shannonCapacity_bddAbove
import Theorems.Thm_GroupTheoreticShannonCapacity_strongPower_cohomomorphism_of_cohomomorphism

set_option autoImplicit true
open GroupTheoreticShannonCapacity
namespace GroupTheoreticShannonCapacity
theorem _root_.solution (G : SimpleGraph V) (H : SimpleGraph W)
    [Fintype V] [Fintype W] (f : V → W)
    (hf : ∀ u v, u ≠ v → ¬G.Adj u v → f u ≠ f v ∧ ¬H.Adj (f u) (f v)) :
    shannonCapacity G ≤ shannonCapacity H := by
  simp only [shannonCapacity]
  apply ciSup_le
  intro n
  apply le_ciSup_of_le (shannonCapacity_bddAbove H) n
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  have hfn := strongPower_cohomomorphism_of_cohomomorphism G H f hf (n + 1)
  have hindep := independenceNumber_le_of_cohomomorphism
    (strongPower G (n + 1)) (strongPower H (n + 1)) (fun x i => f (x i)) hfn
  exact_mod_cast hindep
end GroupTheoreticShannonCapacity
