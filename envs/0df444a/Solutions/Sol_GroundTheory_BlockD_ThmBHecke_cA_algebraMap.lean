-- Prove2me | solution 1 for GroundTheory.BlockD.ThmBHecke.cA_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:00:02.569611+00:00
-- url     : https://prove2.me/submissions/e67dcbbe-74ee-4ad4-bc39-9c6f2e563ff9

import Mathlib
import Definitions.Def_GroundTheory_IdeleRoots_TorusPowers_HeckeTensor
import Definitions.Def_GroundTheory_IdeleRoots_TorusPowers_HeckeIdem
import Theorems.Thm_GroundTheory_BlockD_ThmBHecke_algebraMap_AE_eq
import Theorems.Thm_GroundTheory_BlockD_ThmBHecke_cA_tmul

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
  GroundTheory.Global.SemiLocal
open GroundTheory GroundTheory.BlockD
open GroundTheory.BlockD.ThmBHecke
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E}
namespace GroundTheory.BlockD.ThmBHecke
theorem _root_.solution (a : AF F) :
    cA σ (algebraMap (AF F) (AE F E) a) = algebraMap (AF F) (AE F E) a := by
  rw [algebraMap_AE_eq, cA_tmul, map_one]
end GroundTheory.BlockD.ThmBHecke
