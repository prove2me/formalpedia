-- Prove2me | solution 1 for GlobalTheory.IdxInt.Fubini.relIndex_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:06:20.298517+00:00
-- url     : https://prove2.me/submissions/238bba15-a485-4e86-a015-f6e6319b4e69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CintTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralProdFubini

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.IdxInt
open scoped Pointwise Classical
open GlobalTheory GlobalTheory.IdxInt GlobalTheory.IdxInt.Fubini
variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W']
namespace GlobalTheory.IdxInt.Fubini
theorem _root_.solution (H K : AddSubgroup W) (H' K' : AddSubgroup W') :
    (H.prod H').relIndex (K.prod K') = H.relIndex K * H'.relIndex K' := by
  unfold AddSubgroup.relIndex
  rw [← AddSubgroup.index_prod,
    ← AddSubgroup.index_comap_of_surjective ((H.addSubgroupOf K).prod (H'.addSubgroupOf K'))
      (f := (AddSubgroup.prodEquiv K K').toAddMonoidHom) (AddSubgroup.prodEquiv K K').surjective]
  congr 1
end GlobalTheory.IdxInt.Fubini
