-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.exists_subgroupOf_congruenceSubgroup_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:40:29.05033+00:00
-- url     : https://prove2.me/submissions/42951797-6dfd-4e31-bad8-e98111be590a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LeviCartan
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_hasBasis_nhds_one


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
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
variable {W : Type*} [AddCommGroup W] [Module ℂ W]
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {U : Set (levi F n β)}
    (hU : U ∈ 𝓝 (1 : levi F n β)) :
    ∃ m, (((congruenceSubgroup F n m).subgroupOf (levi F n β) : Subgroup (levi F n β)) :
      Set (levi F n β)) ⊆ U := by
  have hU' : U ∈ comap (Subtype.val : levi F n β → GL (Fin n) F) (𝓝 (1 : GL (Fin n) F)) := by
    rw [nhds_subtype] at hU
    exact hU
  obtain ⟨m, -, hm⟩ :=
    ((hasBasis_nhds_one F n).comap (Subtype.val : levi F n β → GL (Fin n) F)).mem_iff.1 hU'
  exact ⟨m, by rw [Subgroup.coe_subgroupOf]; exact hm⟩
end GroundTheory.Automorphic.Parabolic
