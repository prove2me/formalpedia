-- Prove2me | solution 1 for GroundTheory.Automorphic.fixedMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:24:33.412868+00:00
-- url     : https://prove2.me/submissions/cfa45d0f-065f-4297-a096-2db1aa528377

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_StabilizerOf
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Theorems.Thm_GroundTheory_Automorphic_coe_fixedMap_apply

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
    {σ : Representation ℂ G W} {K : Subgroup G} {f : Representation.IntertwiningMap ρ σ}
    (hf : Function.Injective f) : Function.Injective (fixedMap ρ f K) :=
  fun x y h => Subtype.ext (hf (by simpa [Subtype.ext_iff, coe_fixedMap_apply] using h))
end GroundTheory.Automorphic
