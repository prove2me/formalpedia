-- Prove2me | solution 1 for GroundTheory.BlockD.ThmBHecke.isPlaceIdem_placeIdem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:57:55.87274+00:00
-- url     : https://prove2.me/submissions/51e59964-c4da-49bf-a679-18aa0af525c4

import Mathlib
import Definitions.Def_GroundTheory_IdeleRoots_TorusPowers_HeckeTensor
import Definitions.Def_GroundTheory_IdeleRoots_TorusPowers_HeckeIdem
import Theorems.Thm_GroundTheory_BlockD_ThmBHecke_finSingleOne_self
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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) : IsPlaceIdem F v (placeIdem v) :=
  ⟨finSingleOne v, rfl, finSingleOne_self v, fun _ h ↦ finSingleOne_of_ne h⟩
end GroundTheory.BlockD.ThmBHecke
