-- Prove2me | solution 1 for GroundTheory.Automorphic.heckeAct_mem_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:23:47.041177+00:00
-- url     : https://prove2.me/submissions/84204233-3a3e-46ab-a86f-319a03febb7e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HaarCosets
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology MeasureTheory
open scoped Pointwise ENNReal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {μ} {ρ : Representation ℂ G V}
omit [IsTopologicalGroup G] [BorelSpace G]
namespace GroundTheory.Automorphic
theorem _root_.solution {f : G → ℂ} {v : V} (hfin : (range fun g => f g • ρ g v).Finite)
    {X : Submodule ℂ V} (hX : ∀ g, f g • ρ g v ∈ X) : heckeAct μ ρ f v ∈ X := by
  rw [heckeAct_eq_sum hfin]
  refine Submodule.sum_mem _ fun w hw => Submodule.smul_mem _ _ ?_
  obtain ⟨g, rfl⟩ := (Set.Finite.mem_toFinset _).1 hw
  exact hX g
end GroundTheory.Automorphic
