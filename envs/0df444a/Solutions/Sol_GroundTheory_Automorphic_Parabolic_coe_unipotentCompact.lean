-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.coe_unipotentCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:30:54.149821+00:00
-- url     : https://prove2.me/submissions/73d1b8fd-86a4-42f0-8de6-c99c5393dc9f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicLocal
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_unipotentCompact
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
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
theorem _root_.solution (e : ℕ) :
    (unipotentCompact F n β e : Set (unipotentRadical F n β)) =
      Subtype.val ⁻¹' (conjHomeomorph (rankTorus F n β e) ⁻¹' (integralGL F n : Set _)) := by
  ext u
  simp only [SetLike.mem_coe, mem_unipotentCompact, Set.mem_preimage]
  rfl
end GroundTheory.Automorphic.Parabolic
