-- Prove2me | solution 1 for GroundTheory.Automorphic.map_coinvariantsKer_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:03:00.873505+00:00
-- url     : https://prove2.me/submissions/fec12919-5b39-455c-a627-929e40ea7ca5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_StabilizerOf
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep

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
open Set Filter Topology
variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V)
namespace GroundTheory.Automorphic
theorem _root_.solution {W : Type*} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G W} (f : Representation.IntertwiningMap ρ σ) (H : Subgroup G) :
    coinvariantsKer ρ H ≤ (coinvariantsKer σ H).comap f.toLinearMap := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨h, v⟩, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_comap, map_sub, MonoidHom.coe_comp,
    Function.comp_apply, Subgroup.coe_subtype, Representation.IntertwiningMap.toLinearMap_apply,
    f.isIntertwining]
  exact sub_mem_coinvariantsKer h.2 (f v)
end GroundTheory.Automorphic
