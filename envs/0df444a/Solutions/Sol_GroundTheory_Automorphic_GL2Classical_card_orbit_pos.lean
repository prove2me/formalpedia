-- Prove2me | solution 1 for GroundTheory.Automorphic.GL2Classical.card_orbit_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:48:46.339635+00:00
-- url     : https://prove2.me/submissions/f7faee2f-95fc-4065-83b8-b24b8c31f546

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
theorem _root_.solution {K : Subgroup G} {v : E} (hv : (Set.range fun k : K => ρ k v).Finite) :
    0 < hv.toFinset.card :=
  Finset.card_pos.2 ⟨v, by rw [Set.Finite.mem_toFinset]; exact ⟨1, by simp⟩⟩
end GroundTheory.Automorphic.GL2Classical
