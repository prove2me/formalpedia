-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.smul_mem_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:07:49.329293+00:00
-- url     : https://prove2.me/submissions/bd70cd20-cc28-44df-838a-c7b2cf9a3a5e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_CoeNormEqProdSmulNorm
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_KeyLemma
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_FrobeniusLift_coe_field
import Theorems.Thm_GroundTheory_LocalField_Abstract_mem_fixedModule_frobeniusClosure


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open ProfiniteInteger
open GroundTheory.LocalField.Abstract.ClassFieldData
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A} {K L : OpenSubgroup G}
namespace GroundTheory.LocalField.Abstract.ClassFieldData
theorem _root_.solution [IsDiscreteModule G A] (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
    (s : D.FrobeniusLift K) {g : G}
    (hgJ : ∀ y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker),
      g • y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker))
    (hcomm : ∀ y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker), s.elt • g • y = g • s.elt • y)
    {y : A} (hy : y ∈ fixedModule A ((s.field L hLK : OpenSubgroup G) : Subgroup G)) :
    g • y ∈ fixedModule A ((s.field L hLK : OpenSubgroup G) : Subgroup G) := by
  rw [FrobeniusLift.coe_field, mem_fixedModule_frobeniusClosure] at hy ⊢
  exact ⟨hgJ y hy.1, by rw [hcomm y hy.1, hy.2]⟩
end GroundTheory.LocalField.Abstract.ClassFieldData
