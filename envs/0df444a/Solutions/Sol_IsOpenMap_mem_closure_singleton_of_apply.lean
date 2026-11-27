-- Prove2me | solution 1 for IsOpenMap.mem_closure_singleton_of_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:49:59.93517+00:00
-- url     : https://prove2.me/submissions/36c48177-68cc-4ce6-99ea-5bc697ea0600

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_GenericPointImage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsOpenMap
namespace IsOpenMap
theorem _root_.solution {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {f : A → B} (hopen : IsOpenMap f) (hinj : Function.Injective f)
    {a b : A} (h : f b ∈ closure ({f a} : Set B)) : b ∈ closure ({a} : Set A) := by
  rw [mem_closure_iff]
  intro O hO hbO
  obtain ⟨y, hymem, hy⟩ := (mem_closure_iff.mp h) (f '' O) (hopen O hO) ⟨b, hbO, rfl⟩
  obtain ⟨z, hzO, hz⟩ := hymem
  rw [Set.mem_singleton_iff] at hy
  have hza : z = a := hinj (hz.trans hy)
  subst hza
  exact ⟨z, hzO, rfl⟩
end IsOpenMap
