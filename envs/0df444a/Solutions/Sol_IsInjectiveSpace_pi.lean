-- Prove2me | solution 1 for IsInjectiveSpace.pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:31:35.697816+00:00
-- url     : https://prove2.me/submissions/f4d6ef2f-d999-46f0-b84f-227065036ca8

import Mathlib.Topology.ContinuousMap.T0Sierpinski
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Sets.Opens
import Definitions.Def_Scott1972_ContinuousLattice_Injective

set_option autoImplicit true
open Topology TopologicalSpace
universe u v w
namespace IsInjectiveSpace
theorem _root_.solution {ι : Type w} (D : ι → Type v) [∀ i, TopologicalSpace (D i)]
    (h : ∀ i, IsInjectiveSpace.{u} (D i)) : IsInjectiveSpace.{u} (∀ i, D i) := by
  intro X Y _ _ e he f
  choose g hg using fun i =>
    h i e he ⟨fun x => f x i, (continuous_apply i).comp f.continuous⟩
  refine ⟨⟨fun y i => g i y, continuous_pi fun i => (g i).continuous⟩, fun x => ?_⟩
  funext i
  exact hg i x
end IsInjectiveSpace
