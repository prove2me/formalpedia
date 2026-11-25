-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.smul_norm_inf_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:45:03.32208+00:00
-- url     : https://prove2.me/submissions/a317622f-d2ba-4fea-96ca-7e5f2dc7e591

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_CoeNormEqProdSmulNorm
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_KeyLemma
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_map_conj_inf_ker_self
import Theorems.Thm_GroundTheory_LocalField_Abstract_smul_norm_of_map_eq


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
omit [TotallyDisconnectedSpace G]
namespace GroundTheory.LocalField.Abstract.ClassFieldData
theorem _root_.solution (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal] {g : G}
    (hg : g ∈ (K : Subgroup G)) (y : fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) :
    g • (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) y : A) =
      norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
        ⟨g • (y : A), smul_mem_fixedModule_inf_ker hLK hg y.2⟩ :=
  smul_norm_of_map_eq g (map_conj_inf_ker_self hg) (map_conj_inf_ker hLK hg) y
end GroundTheory.LocalField.Abstract.ClassFieldData
