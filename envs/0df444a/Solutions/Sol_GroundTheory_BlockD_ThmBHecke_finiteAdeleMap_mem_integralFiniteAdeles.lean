-- Prove2me | solution 1 for GroundTheory.BlockD.ThmBHecke.finiteAdeleMap_mem_integralFiniteAdeles
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:39:55.467868+00:00
-- url     : https://prove2.me/submissions/42f49109-06e3-40f2-8495-3694b06f8419

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_ThmBInHecke
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteTensor
import Definitions.Def_GroundTheory_IdeleRoots_TorusPowers_HeckeTensor
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_finiteAdeleMap_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.AdeleBaseChange.finiteAdeleMap_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped TensorProduct NumberField.AdeleRing
open NumberField IsDedekindDomain HeckeCharacterZeroLocus.ThmBIn GroundTheory.Global GroundTheory.Global.AdeleBaseChange
open GroundTheory GroundTheory.BlockD
open GroundTheory.BlockD.ThmBHecke
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GroundTheory.BlockD.ThmBHecke
theorem _root_.solution {a : Af F} (ha : a ∈ intAf F) :
    finiteAdeleMap F E a ∈ integralFiniteAdeles (𝓞 E) E := fun w ↦ by
  rw [finiteAdeleMap_apply]
  exact mapsTo_completionMap _ w (ha _)
end GroundTheory.BlockD.ThmBHecke
