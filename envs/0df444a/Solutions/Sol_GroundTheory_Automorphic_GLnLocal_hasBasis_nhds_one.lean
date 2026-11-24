-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.hasBasis_nhds_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:40:56.402902+00:00
-- url     : https://prove2.me/submissions/604578e5-6d48-4040-9a19-8c090bb4a2a2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_isCompact_integralGL
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_congruenceSubgroup_le
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_congruenceSubgroup_antitone

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
open ValuativeRel Topology Filter Set
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] (n : ℕ)
variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Automorphic.GLnLocal
theorem _root_.solution :
    (𝓝 (1 : GL (Fin n) F)).HasBasis (fun _ : ℕ => True)
      fun m => (congruenceSubgroup F n m : Set (GL (Fin n) F)) := by
  refine ⟨fun U => ⟨fun hU => ?_, fun ⟨m, _, hm⟩ => Filter.mem_of_superset
    ((isOpen_congruenceSubgroup F n m).mem_nhds (one_mem _)) hm⟩⟩
  have hclosed : ∀ m, IsClosed ((congruenceSubgroup F n m : Set (GL (Fin n) F)) ∩ (interior U)ᶜ) :=
    fun m => (isClosed_congruenceSubgroup F n m).inter isOpen_interior.isClosed_compl
  have hempty : (integralGL F n : Set (GL (Fin n) F)) ∩
      ⋂ m, ((congruenceSubgroup F n m : Set (GL (Fin n) F)) ∩ (interior U)ᶜ) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun g ⟨_, hg⟩ => ?_
    rw [Set.mem_iInter] at hg
    have h1 : g ∈ ⨅ m, congruenceSubgroup F n m := Subgroup.mem_iInf.mpr fun m => (hg m).1
    rw [iInf_congruenceSubgroup, Subgroup.mem_bot] at h1
    exact (hg 0).2 (by rw [h1]; exact mem_interior_iff_mem_nhds.mpr hU)
  have hanti : Antitone fun m => (congruenceSubgroup F n m : Set (GL (Fin n) F)) ∩ (interior U)ᶜ :=
    fun m m' h => Set.inter_subset_inter_left _
      (SetLike.coe_subset_coe.mpr (congruenceSubgroup_antitone F n h))
  obtain ⟨m, hm⟩ :=
    (isCompact_integralGL F n).elim_directed_family_closed _ hclosed hempty hanti.directed_ge
  refine ⟨m, trivial, fun g hg => interior_subset (by_contra fun h => ?_)⟩
  have : g ∈ (integralGL F n : Set (GL (Fin n) F)) ∩
      ((congruenceSubgroup F n m : Set (GL (Fin n) F)) ∩ (interior U)ᶜ) :=
    ⟨congruenceSubgroup_le F n m hg, hg, h⟩
  rw [hm] at this
  exact this
end GroundTheory.Automorphic.GLnLocal
