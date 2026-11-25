-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.isSmooth_jacquetRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:39:07.712621+00:00
-- url     : https://prove2.me/submissions/ca74dd8a-b5eb-4dd1-af73-e3a025903ea0

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_Induction
import Definitions.Def_GroundTheory_AutomorphicForms_InductionJacquet
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicLocal
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_invSqrtModular_leviIncl_of_mem

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
open Matrix Iwasawa GLnLocal Topology Filter Set MeasureTheory Measure
open scoped NNReal
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) F) V)
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (hπ : IsSmooth π) : IsSmooth (jacquetRep F n β π) := by
  intro x
  obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective _ x
  refine Subgroup.isOpen_mono (H₁ := (stabilizerOf π v ⊓ integralGL F n).subgroupOf (levi F n β))
    (fun m hm => ?_) ?_
  · rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hm
    rw [mem_stabilizerOf, jacquetRep_mk, mem_stabilizerOf.1 hm.1,
      invSqrtModular_leviIncl_of_mem m hm.2, one_smul]
  · rw [Subgroup.coe_subgroupOf, Subgroup.coe_inf]
    exact ((hπ v).inter (isOpen_integralGL F n)).preimage continuous_subtype_val
end GroundTheory.Automorphic.Parabolic
