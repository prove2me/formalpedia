-- Prove2me | solution 1 for GroundTheory.Global.cycHerbrand_eq_of_surjective_of_finite_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:50:02.52536+00:00
-- url     : https://prove2.me/submissions/d76d9e92-a575-4a8d-86e5-83d85dcf36e1

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsExact
import Theorems.Thm_GroundTheory_Global_cycNorm_cycSubOne
import Theorems.Thm_GroundTheory_Global_cycSubOne_cycNorm
import Theorems.Thm_GroundTheory_Global_cycSub_apply
import Theorems.Thm_GroundTheory_Global_normHom_apply
import Theorems.Thm_GroundTheory_Global_piRep_apply
import Theorems.Thm_GroundTheory_GroupCoh_hasHerbrandQuotient_of_finite
import Theorems.Thm_GroundTheory_GroupCoh_herbrandQuotient_eq_mul_of_shortExact
import Theorems.Thm_GroundTheory_GroupCoh_herbrandQuotient_eq_one_of_finite
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
attribute [local simp] GroundTheory.Global.piRep_apply
attribute [local simp] GroundTheory.GroupCoh.restrictEnd_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh
variable {G A B C : Type*} [Group G] [Fintype G] [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C]
namespace GroundTheory.Global
theorem _root_.solution (ρB : Representation ℤ G B)
    (ρC : Representation ℤ G C) (σ : G) {p : B →+ C} (hp : Function.Surjective p)
    [Finite p.ker] (hpG : ∀ g b, p (ρB g b) = ρC g (p b))
    (hC : HasHerbrandQuotient (cycSubOne ρC σ) (cycNorm ρC)) :
    cycHerbrand ρB σ = cycHerbrand ρC σ := by
  have hfK : ∀ x ∈ p.ker, cycSubOne ρB σ x ∈ p.ker := by
    intro x hx
    rw [AddMonoidHom.mem_ker] at hx ⊢
    rw [cycSubOne_apply, map_sub, hpG, hx, map_zero, sub_zero]
  have hgK : ∀ x ∈ p.ker, cycNorm ρB x ∈ p.ker := by
    intro x hx
    rw [AddMonoidHom.mem_ker] at hx ⊢
    rw [cycNorm_apply, map_sum]
    simp [hpG, hx]
  have hfgK : ∀ x, restrictEnd (cycSubOne ρB σ) p.ker hfK
      (restrictEnd (cycNorm ρB) p.ker hgK x) = 0 := fun x =>
    Subtype.ext (by simp [cycSubOne_cycNorm])
  have hgfK : ∀ x, restrictEnd (cycNorm ρB) p.ker hgK
      (restrictEnd (cycSubOne ρB σ) p.ker hfK x) = 0 := fun x =>
    Subtype.ext (by simp [cycNorm_cycSubOne])
  have hA : HasHerbrandQuotient (restrictEnd (cycSubOne ρB σ) p.ker hfK)
      (restrictEnd (cycNorm ρB) p.ker hgK) := hasHerbrandQuotient_of_finite _ _
  have hex : Function.Exact p.ker.subtype p := by
    intro b
    simp
  rw [cycHerbrand, cycHerbrand,
    herbrandQuotient_eq_mul_of_shortExact p.ker.subtype_injective hp hex
      (fun _ => rfl) (fun _ => rfl)
      (fun b => by rw [cycSubOne_apply, cycSubOne_apply, map_sub, hpG])
      (fun b => by rw [cycNorm_apply, cycNorm_apply, map_sum]; simp only [hpG])
      (cycSubOne_cycNorm ρB σ) (cycNorm_cycSubOne ρB σ) hA hC,
    herbrandQuotient_eq_one_of_finite hfgK hgfK, one_mul]
end GroundTheory.Global
