-- Prove2me | solution 1 for GroundTheory.BlockD.ThmBHecke.algebraMap_mem_integralFiniteAdeles
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:37:10.38501+00:00
-- url     : https://prove2.me/submissions/586309a7-fb0b-4ce3-8bdc-88ede43cd513

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_ThmBInHecke
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteTensor
import Definitions.Def_GroundTheory_IdeleRoots_TorusPowers_HeckeTensor
import Theorems.Thm_GroundTheory_Global_coe_mem_adicCompletionIntegers_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped TensorProduct NumberField.AdeleRing
open NumberField IsDedekindDomain HeckeCharacterZeroLocus.ThmBIn GroundTheory.Global GroundTheory.Global.AdeleBaseChange
open GroundTheory GroundTheory.BlockD
open GroundTheory.BlockD.ThmBHecke
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GroundTheory.BlockD.ThmBHecke
theorem _root_.solution (x : 𝓞 E) :
    algebraMap E (FiniteAdeleRing (𝓞 E) E) (x : E) ∈ integralFiniteAdeles (𝓞 E) E := fun w ↦
  (coe_mem_adicCompletionIntegers_iff w (x : E)).2 (w.valuation_le_one x)
end GroundTheory.BlockD.ThmBHecke
