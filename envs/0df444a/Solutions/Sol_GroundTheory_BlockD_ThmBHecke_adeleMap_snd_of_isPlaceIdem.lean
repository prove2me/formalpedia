-- Prove2me | solution 1 for GroundTheory.BlockD.ThmBHecke.adeleMap_snd_of_isPlaceIdem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:16:59.458069+00:00
-- url     : https://prove2.me/submissions/d3919055-5d3f-476d-8d81-2026906d37e6

import Mathlib
import Definitions.Def_GroundTheory_IdeleRoots_TorusPowers_HeckeTensor
import Definitions.Def_GroundTheory_IdeleRoots_TorusPowers_HeckeIdem
import Theorems.Thm_GroundTheory_BlockD_ThmBHecke_adeleMap_snd_apply

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
open Classical
namespace GroundTheory.BlockD.ThmBHecke
theorem _root_.solution {v : HeightOneSpectrum (𝓞 F)} {ε : AF F} (h : IsPlaceIdem F v ε)
    (w : HeightOneSpectrum (𝓞 E)) :
    (adeleMap F E ε).2 w = if below F w = v then 1 else 0 := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  rw [adeleMap_snd_apply]
  split_ifs with hw
  · have : (pairA F 0 α).2 (below F w) = 1 := by rw [hw]; exact h1
    rw [this, map_one]
  · have : (pairA F 0 α).2 (below F w) = 0 := h0 _ hw
    rw [this, map_zero]
end GroundTheory.BlockD.ThmBHecke
