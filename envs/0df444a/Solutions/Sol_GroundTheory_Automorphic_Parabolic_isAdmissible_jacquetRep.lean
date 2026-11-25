-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.isAdmissible_jacquetRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:51:06.750806+00:00
-- url     : https://prove2.me/submissions/e50b1899-722e-4979-901f-f922ef125564

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_SupercuspidalCoefficients
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleFiniteLength
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_fixedVectors_jacquetRep_congruenceSubgroup
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_congruenceSubgroup_antitone
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_isCompact_congruenceSubgroup
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_subgroupOf_congruenceSubgroup_subset
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_isSmooth_jacquetRep
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_jacquetFixedMap_surjective_congruenceSubgroup
import Theorems.Thm_GroundTheory_Automorphic_fixedVectors_antitone


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
open Matrix Iwasawa GLnLocal Topology Filter Set
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
  {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (hπ : IsAdmissible π) : IsAdmissible (jacquetRep F n β π) := by
  refine ⟨isSmooth_jacquetRep π hπ.1, fun L hLc hLo => ?_⟩
  obtain ⟨m₁, hm₁⟩ := exists_subgroupOf_congruenceSubgroup_subset (hLo.mem_nhds L.one_mem)
  set m := max m₁ 1
  have hle : (congruenceSubgroup F n m).subgroupOf (levi F n β) ≤ L := fun x hx =>
    hm₁ (Subgroup.mem_subgroupOf.2 (congruenceSubgroup_antitone F n (le_max_left _ _)
      (Subgroup.mem_subgroupOf.1 hx)))
  have : FiniteDimensional ℂ (fixedVectors π (congruenceSubgroup F n m)) :=
    hπ.2 _ (isCompact_congruenceSubgroup F n m) (isOpen_congruenceSubgroup F n m)
  have hfin : FiniteDimensional ℂ
      (fixedVectors (jacquetRep F n β π) ((congruenceSubgroup F n m).subgroupOf (levi F n β))) := by
    rw [fixedVectors_jacquetRep_congruenceSubgroup]
    exact Module.Finite.of_surjective _
      (jacquetFixedMap_surjective_congruenceSubgroup β hπ (le_max_right m₁ 1))
  exact Submodule.finiteDimensional_of_le (fixedVectors_antitone _ hle)
end GroundTheory.Automorphic.Parabolic
