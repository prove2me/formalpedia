-- Prove2me | solution 1 for GlobalTheory.BorelUMod.relIndex_prod_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:02:36.516862+00:00
-- url     : https://prove2.me/submissions/8057c96d-12f3-4187-b656-4dcd77e7e356

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUpLatEqSq
import Theorems.Thm_GlobalTheory_LGrp_LeviDatum_IsOpposite_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.LGrp GlobalTheory.BorelUMod Formalism.UG
noncomputable section
open GlobalTheory GlobalTheory.BorelUMod
namespace GlobalTheory.BorelUMod
theorem _root_.solution {G G' : Type} [AddGroup G] [AddGroup G'] (H K : AddSubgroup G) (H' K' : AddSubgroup G') :
    (H.prod H').relIndex (K.prod K') = H.relIndex K * H'.relIndex K' := by
  unfold AddSubgroup.relIndex
  rw [← AddSubgroup.index_prod,
    ← AddSubgroup.index_comap_of_surjective ((H.addSubgroupOf K).prod (H'.addSubgroupOf K'))
      (f := (AddSubgroup.prodEquiv K K').toAddMonoidHom) (AddSubgroup.prodEquiv K K').surjective]
  congr 1
end GlobalTheory.BorelUMod
