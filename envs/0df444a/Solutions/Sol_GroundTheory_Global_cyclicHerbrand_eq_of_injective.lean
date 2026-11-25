-- Prove2me | solution 1 for GroundTheory.Global.cyclicHerbrand_eq_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:54:24.387138+00:00
-- url     : https://prove2.me/submissions/b16f6a63-fd23-4fd2-97b2-2c1eff7e3638

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_RationalForm
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Lattice
import Theorems.Thm_GroundTheory_Global_cycSub_apply
import Theorems.Thm_GroundTheory_Global_cycSub_normHom
import Theorems.Thm_GroundTheory_Global_normHom_apply
import Theorems.Thm_GroundTheory_Global_normHom_cycSub
import Theorems.Thm_GroundTheory_GroupCoh_herbrandQuotient_eq_of_injective_of_finite
import Theorems.Thm_GroundTheory_GroupCoh_restrictEnd_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.cycSub_apply
attribute [local simp] GroundTheory.Global.normHom_apply
attribute [local simp] GroundTheory.GroupCoh.restrictEnd_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh
open scoped TensorProduct
variable {G M M' : Type*} [Group G] [AddCommGroup M] [AddCommGroup M']
namespace GroundTheory.Global
theorem _root_.solution [Fintype G] (ρ : Representation ℤ G M)
    (ρ' : Representation ℤ G M') (σ : G) (φ : M →+ M') (hφ : Function.Injective φ)
    [Finite (M' ⧸ φ.range)] (hcomm : ∀ g x, φ (ρ g x) = ρ' g (φ x)) :
    cyclicHerbrand ρ σ = cyclicHerbrand ρ' σ :=
  herbrandQuotient_eq_of_injective_of_finite (fA := cycSub ρ σ) (gA := normHom ρ)
    (fB := cycSub ρ' σ) (gB := normHom ρ') hφ
    (fun a => by rw [cycSub_apply, cycSub_apply, map_sub, hcomm])
    (fun a => by rw [normHom_apply, normHom_apply, map_sum]; simp only [hcomm])
    (cycSub_normHom ρ' σ) (normHom_cycSub ρ' σ)
end GroundTheory.Global
