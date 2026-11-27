-- Prove2me | solution 1 for Neutral.B1.one_mem_rayUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:52:12.990026+00:00
-- url     : https://prove2.me/submissions/a6bf6aa6-b90f-45e1-b491-4903c2b62c0f

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Topology
open Neutral Neutral.B1
variable (K : Type*) [Field K] [NumberField K]
namespace Neutral.B1
theorem _root_.solution (m₀ : Ideal (𝓞 K)) (mInf : Set (InfinitePlace K)) :
    (1 : Ideles K) ∈ rayUnits K m₀ mInf := by
  refine ⟨fun w _ => ⟨1, by rw [mul_one]; rfl⟩, fun v => ⟨?_, 0, m₀.zero_mem, ?_⟩⟩
  · show Valued.v (1 : v.adicCompletion K) = 1
    exact map_one _
  · show Valued.v ((1 : v.adicCompletion K) - 1) ≤ _
    simp
end Neutral.B1
