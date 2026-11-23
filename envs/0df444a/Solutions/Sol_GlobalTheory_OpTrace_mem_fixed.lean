-- Prove2me | solution 1 for GlobalTheory.OpTrace.mem_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:02.59372+00:00
-- url     : https://prove2.me/submissions/3ebd825f-162e-4b2f-aaa7-4fa23dfd35d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace Pointwise
noncomputable section
open GlobalTheory GlobalTheory.OpTrace
open GlobalTheory.PRep
variable {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
omit [TopologicalSpace G]
namespace GlobalTheory.OpTrace
theorem _root_.solution {ρ : Representation ℂ G V} {K : Subgroup G} {v : V} :
    v ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k v = v :=
  ⟨fun h k hk => by simpa using h ⟨k, hk⟩, fun h k => by simpa using h k k.2⟩
end GlobalTheory.OpTrace
