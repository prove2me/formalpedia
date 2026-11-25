-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.isClosed_unipotentRadical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:08:05.605901+00:00
-- url     : https://prove2.me/submissions/ab85c197-f269-4e5c-a3eb-f0bd08a58ba6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicLocal
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_mem_blockUpper
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_unipotentRadical
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable (F) (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution :
    IsClosed (unipotentRadical F n β : Set (GL (Fin n) F)) := by
  have : (unipotentRadical F n β : Set (GL (Fin n) F)) =
      (⋂ i, ⋂ j, ⋂ (_ : β j < β i), (fun g : GL (Fin n) F => g i j) ⁻¹' {0}) ∩
      ⋂ i, ⋂ j, ⋂ (_ : β i = β j),
        (fun g : GL (Fin n) F => g i j) ⁻¹' {(1 : Matrix (Fin n) (Fin n) F) i j} := by
    ext g
    simp only [SetLike.mem_coe, mem_unipotentRadical, mem_blockUpper, Set.mem_inter_iff,
      Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun ⟨h1, h2⟩ => ⟨fun i j hij => h1 hij, h2⟩,
      fun ⟨h1, h2⟩ => ⟨fun i j hij => h1 i j hij, h2⟩⟩
  rw [this]
  refine IsClosed.inter ?_ ?_ <;>
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_singleton.preimage (continuous_entry F n i j)
end GroundTheory.Automorphic.Parabolic
