-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.tateZeroVal_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:28:41.476278+00:00
-- url     : https://prove2.me/submissions/72a892af-0d3d-4d71-8855-64c6dada0b46

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Unramified

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
variable {K L : OpenSubgroup G}
namespace GroundTheory.LocalField.Abstract.ClassFieldData
theorem _root_.solution (hLK : L ≤ K) (a : fixedModule A (K : Subgroup G)) :
    D.tateZeroVal hLK (a : tateZero A (K : Subgroup G) (L : Subgroup G)) =
      D.valuationMod K (D.relInertiaDegreePNat hLK) a :=
  rfl
end GroundTheory.LocalField.Abstract.ClassFieldData
