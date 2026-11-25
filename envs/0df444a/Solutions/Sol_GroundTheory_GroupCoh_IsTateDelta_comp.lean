-- Prove2me | solution 1 for GroundTheory.GroupCoh.IsTateDelta.comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:36:31.433876+00:00
-- url     : https://prove2.me/submissions/f2167444-015e-47f9-adc1-8e1cae10fb1e

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateUnique
import Definitions.Def_GroundTheory_TateCohomology_TateTransport
import Definitions.Def_GroundTheory_TateCohomology_ResCoresZero
import Definitions.Def_GroundTheory_TateCohomology_TateSubgroupMaps
import Theorems.Thm_GroundTheory_GroupCoh_sq_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable [Fintype G]
open GroundTheory.GroupCoh.IsTateDelta
variable {U V W : Subgroup G} [Fintype U] [Fintype V] [Fintype W]
omit [Fintype G]
namespace GroundTheory.GroupCoh.IsTateDelta
theorem _root_.solution {α : ∀ n : ℤ, resFunctor U.subtype ⋙ tateCohomologyFunctor (R := k) n ⟶
      resFunctor V.subtype ⋙ tateCohomologyFunctor n}
    {β : ∀ n : ℤ, resFunctor V.subtype ⋙ tateCohomologyFunctor (R := k) n ⟶
      resFunctor W.subtype ⋙ tateCohomologyFunctor n}
    (hα : IsTateDelta α) (hβ : IsTateDelta β) : IsTateDelta (fun n => α n ≫ β n) := by
  intro X hX n
  exact sq_comp (hα hX n) (hβ hX n)
end GroundTheory.GroupCoh.IsTateDelta
