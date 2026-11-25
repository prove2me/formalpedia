-- Prove2me | solution 1 for GroundTheory.BlockD.ThmBHecke.mem_integralFiniteAdeles_mul_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:45:49.922372+00:00
-- url     : https://prove2.me/submissions/e611b2ae-e5fc-4c9c-a42f-c9ba8185a8e6

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_ThmBInHecke
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteTensor
import Definitions.Def_GroundTheory_IdeleRoots_TorusPowers_HeckeTensor
import Theorems.Thm_GroundTheory_BlockD_ThmBHecke_algebraMap_mem_integralFiniteAdeles

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
theorem _root_.solution {s : FiniteAdeleRing (𝓞 E) E}
    (hs : s ∈ integralFiniteAdeles (𝓞 E) E) {x : E} (hx : IsIntegral ℤ x) (w : HeightOneSpectrum (𝓞 E)) :
    s w * algebraMap E (w.adicCompletion E) x ∈ w.adicCompletionIntegers E :=
  Subring.mul_mem _ (hs w) (algebraMap_mem_integralFiniteAdeles (⟨x, hx⟩ : 𝓞 E) w)
end GroundTheory.BlockD.ThmBHecke
