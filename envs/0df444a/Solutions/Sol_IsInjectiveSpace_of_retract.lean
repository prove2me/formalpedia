-- Prove2me | solution 1 for IsInjectiveSpace.of_retract
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:28:37.871076+00:00
-- url     : https://prove2.me/submissions/271d89ae-98ea-42c8-bf76-b0330e03d74a

import Mathlib.Topology.ContinuousMap.T0Sierpinski
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Sets.Opens
import Definitions.Def_Scott1972_ContinuousLattice_Injective

set_option autoImplicit true
open Topology TopologicalSpace
universe u v w
namespace IsInjectiveSpace
theorem _root_.solution {D : Type v} {D' : Type v}
    [TopologicalSpace D] [TopologicalSpace D'] (hD : IsInjectiveSpace.{u} D)
    (s : C(D', D)) (r : C(D, D')) (hrs : ∀ d, r (s d) = d) :
    IsInjectiveSpace.{u} D' := by
  intro X Y _ _ e he f
  obtain ⟨g, hg⟩ := hD e he (s.comp f)
  refine ⟨r.comp g, fun x => ?_⟩
  show r (g (e x)) = f x
  rw [hg x]
  exact hrs (f x)
end IsInjectiveSpace
