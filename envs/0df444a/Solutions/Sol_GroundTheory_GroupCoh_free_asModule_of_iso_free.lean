-- Prove2me | solution 1 for GroundTheory.GroupCoh.free_asModule_of_iso_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:10:44.706728+00:00
-- url     : https://prove2.me/submissions/d77a025a-1c95-4cd0-89a3-2db05ddd9d8d

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_TateAddEquivAbelianizationTateClass
import Definitions.Def_GroundTheory_TateCohomology_PGroupFixed
import Definitions.Def_GroundTheory_TateCohomology_PGroupFree

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
open CategoryTheory Limits groupHomology Representation Finsupp
open scoped MonoidAlgebra
universe u
variable {k G : Type u} [Field k] [Group G] [Fintype G] {p : ℕ} [Fact p.Prime] [CharP k p]
namespace GroundTheory.GroupCoh
theorem _root_.solution {k G : Type u} [CommRing k] [Group G] {M : Rep.{u} k G}
    {ι : Type u} (e : Rep.free k G ι ≅ M) : Module.Free k[G] M.ρ.asModule := by
  let φ := Representation.equivOfIso e
  have := Representation.free_asModule_free k G ι
  exact Module.Free.of_equiv (LinearEquiv.ofLinearMap
    (IntertwiningMap.equivLinearMapAsModule (ρ := (Rep.free k G ι).ρ) (σ := M.ρ) φ.toIntertwiningMap)
    (IntertwiningMap.equivLinearMapAsModule (ρ := M.ρ) (σ := (Rep.free k G ι).ρ)
      φ.symm.toIntertwiningMap)
    (LinearMap.ext fun x => φ.apply_symm_apply x) (LinearMap.ext fun x => φ.symm_apply_apply x))
end GroundTheory.GroupCoh
