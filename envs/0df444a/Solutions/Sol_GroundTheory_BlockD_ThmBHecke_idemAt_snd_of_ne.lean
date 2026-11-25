-- Prove2me | solution 1 for GroundTheory.BlockD.ThmBHecke.idemAt_snd_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:02:30.032484+00:00
-- url     : https://prove2.me/submissions/789b1b0c-344f-4b4c-a307-67914bcfde99

import Mathlib
import Definitions.Def_GroundTheory_IdeleRoots_TorusPowers_HeckeTensor
import Definitions.Def_GroundTheory_IdeleRoots_TorusPowers_HeckeIdem
import Theorems.Thm_GroundTheory_BlockD_ThmBHecke_finSingleOne_of_ne

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
namespace GroundTheory.BlockD.ThmBHecke
theorem _root_.solution {P w : HeightOneSpectrum (𝓞 E)} (h : w ≠ P) : (idemAt P).2 w = 0 :=
  finSingleOne_of_ne h
end GroundTheory.BlockD.ThmBHecke
