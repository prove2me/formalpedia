-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.independenceNumber_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:36:28.3846+00:00
-- url     : https://prove2.me/submissions/6564b546-d2d3-45b5-84cd-41b99649cd91

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Theorems.Thm_GroupTheoreticShannonCapacity_independenceNumber_le_of_cohomomorphism
section
namespace GroupTheoreticShannonCapacity
private lemma iso_is_cohomomorphism {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) :
    ∀ u v, u ≠ v → ¬G.Adj u v → f u ≠ f v ∧ ¬H.Adj (f u) (f v) := by
  intro u v huv hnadj
  exact ⟨fun h => huv (f.injective h), fun hadj => hnadj (f.map_rel_iff'.mp hadj)⟩
private lemma indepNum_le_of_iso {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) :
    G.indepNum ≤ H.indepNum :=
  independenceNumber_le_of_cohomomorphism G H f (iso_is_cohomomorphism f)
end GroupTheoreticShannonCapacity
end

set_option autoImplicit true
open GroupTheoreticShannonCapacity
namespace GroupTheoreticShannonCapacity
theorem _root_.solution {W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) :
    G.indepNum = H.indepNum :=
  le_antisymm (indepNum_le_of_iso f) (indepNum_le_of_iso f.symm)
end GroupTheoreticShannonCapacity
