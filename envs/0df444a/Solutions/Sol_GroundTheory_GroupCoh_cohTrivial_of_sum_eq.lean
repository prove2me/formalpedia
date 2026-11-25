-- Prove2me | solution 1 for GroundTheory.GroupCoh.cohTrivial_of_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:08:21.216083+00:00
-- url     : https://prove2.me/submissions/cfa28e01-b0ab-432b-91bb-6cab987d3042

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_CoindOne
import Definitions.Def_GroundTheory_TateCohomology_UniquelyDivisible
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
import Theorems.Thm_GroundTheory_GroupCoh_exists_sum_eq_subgroup
import Theorems.Thm_GroundTheory_GroupCoh_tateAcyclic_of_sum_eq


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
open scoped MonoidAlgebra
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable {V : Type*} [AddCommGroup V] [Module k V]
namespace GroundTheory.GroupCoh
theorem _root_.solution [Fintype G] (M : Rep.{u} k G) (φ : M.V →ₗ[k] M.V)
    (hφ : ∀ m : M, ∑ g : G, M.ρ g (φ (M.ρ g⁻¹ m)) = m) : CohTrivial M := fun S _ => by
  obtain ⟨ψ, hψ⟩ := exists_sum_eq_subgroup M.ρ φ hφ S
  exact tateAcyclic_of_sum_eq (res S.subtype M) ψ hψ
end GroundTheory.GroupCoh
