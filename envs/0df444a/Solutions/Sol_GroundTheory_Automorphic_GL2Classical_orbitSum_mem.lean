-- Prove2me | solution 1 for GroundTheory.Automorphic.GL2Classical.orbitSum_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:48:51.249969+00:00
-- url     : https://prove2.me/submissions/482bc13d-a2e7-4da9-8474-55ad260b2730

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2Classical_UnitaryEigenSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.GL2Classical
variable {G : Type*} [Group G] {E : Type*} [AddCommGroup E] [Module ℂ E]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (ρ : Representation ℂ G E) (ι : E →ₗ[ℂ] H) (T : Submodule ℂ E)
variable {ρ}
namespace GroundTheory.Automorphic.GL2Classical
theorem _root_.solution {K : Subgroup G} {v : E} (hv : (Set.range fun k : K => ρ k v).Finite)
    {Y : Submodule ℂ E} (hY : ∀ g, ∀ y ∈ Y, ρ g y ∈ Y) (hvY : v ∈ Y) : orbitSum ρ K v hv ∈ Y := by
  refine Submodule.sum_mem _ fun w hw => ?_
  rw [Set.Finite.mem_toFinset] at hw
  obtain ⟨k, rfl⟩ := hw
  exact hY _ _ hvY
end GroundTheory.Automorphic.GL2Classical
