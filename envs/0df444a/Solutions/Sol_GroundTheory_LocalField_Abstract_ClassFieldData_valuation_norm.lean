-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.valuation_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:49:09.544821+00:00
-- url     : https://prove2.me/submissions/6ac769c5-4c82-4e0b-a02e-a8da9f5080fd

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_RelIndexSup
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Theorems.Thm_GroundTheory_LocalField_Abstract_inertiaDegree_eq_mul
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_valuation_pow
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_valuation_eq_iff
import Theorems.Thm_GroundTheory_LocalField_Abstract_norm_norm


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
open GroundTheory.LocalField.Abstract.ClassFieldData
open ProfiniteInteger
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type*} [CommGroup A] [MulDistribMulAction G A] (D : ClassFieldData G A)
namespace GroundTheory.LocalField.Abstract.ClassFieldData
theorem _root_.solution {K L : OpenSubgroup G} (hLK : L ≤ K) (a : fixedModule A (L : Subgroup G)) :
    D.valuation K (norm A (K : Subgroup G) (L : Subgroup G) a) = D.valuation L a ^ relInertiaDegree D.deg K L := by
  rw [valuation_eq_iff, norm_norm (M := (L : Subgroup G)) (L := (K : Subgroup G)) hLK le_top, ← valuation_pow,
    ← pow_mul, inertiaDegree_eq_mul D.surjective_deg (K := (K : Subgroup G)) (L := (L : Subgroup G)) hLK]
end GroundTheory.LocalField.Abstract.ClassFieldData
