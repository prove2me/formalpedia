-- Prove2me | solution 1 for GroundTheory.Global.cycHerbrand_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:25:14.245052+00:00
-- url     : https://prove2.me/submissions/efc56427-ee29-4619-8fae-1e236eb18e75

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsExact
import Theorems.Thm_GroundTheory_Global_cycHerbrand_eq_mul_of_exact
import Theorems.Thm_GroundTheory_Global_cycSub_apply
import Theorems.Thm_GroundTheory_Global_normHom_apply
import Theorems.Thm_GroundTheory_Global_piRep_apply
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
theorem _root_.solution (ρA : Representation ℤ G A) (ρB : Representation ℤ G B) (σ : G)
    (hA : HasHerbrandQuotient (cycSubOne ρA σ) (cycNorm ρA))
    (hB : HasHerbrandQuotient (cycSubOne ρB σ) (cycNorm ρB)) :
    cycHerbrand (ρA.prod ρB) σ = cycHerbrand ρA σ * cycHerbrand ρB σ := by
  have : Finite (B ⧸ (AddMonoidHom.snd A B).range) := by
    rw [AddMonoidHom.range_eq_top.2 (fun b => ⟨(0, b), rfl⟩)]
    infer_instance
  refine cycHerbrand_eq_mul_of_exact ρA (ρA.prod ρB) ρB σ (i := AddMonoidHom.inl A B)
    (p := AddMonoidHom.snd A B) (fun a a' h => congrArg Prod.fst h) ?_ (fun g a => ?_)
    (fun g b => rfl) hA hB
  · rintro ⟨a, b⟩
    simp only [AddMonoidHom.coe_snd, Set.mem_range, AddMonoidHom.inl_apply, Prod.ext_iff]
    constructor
    · rintro rfl
      exact ⟨a, rfl, rfl⟩
    · rintro ⟨a', -, rfl⟩
      rfl
  · exact Prod.ext rfl (map_zero (ρB g)).symm
end GroundTheory.Global
