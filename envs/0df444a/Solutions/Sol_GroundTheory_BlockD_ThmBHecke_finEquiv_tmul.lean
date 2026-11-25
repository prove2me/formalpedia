-- Prove2me | solution 1 for GroundTheory.BlockD.ThmBHecke.finEquiv_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:37:12.378847+00:00
-- url     : https://prove2.me/submissions/e28f546f-94f9-47b2-b8ad-ca568e749238

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_ThmBInHecke
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteTensor
import Definitions.Def_GroundTheory_IdeleRoots_TorusPowers_HeckeTensor
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_finiteTensorEquiv_tmul


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
theorem _root_.solution (a : Af F) (x : E) :
    finEquiv F E (a ⊗ₜ x) = algebraMap E (FiniteAdeleRing (𝓞 E) E) x * finiteAdeleMap F E a := by
  change finiteTensorEquiv F E (Algebra.TensorProduct.comm F (Af F) E (a ⊗ₜ x)) = _
  rw [Algebra.TensorProduct.comm_tmul, finiteTensorEquiv_tmul]
end GroundTheory.BlockD.ThmBHecke
