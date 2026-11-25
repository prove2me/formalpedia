-- Prove2me | solution 1 for GroundTheory.BlockD.ThmBHecke.finSingleOne_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:49:52.983205+00:00
-- url     : https://prove2.me/submissions/e6663fe7-c910-404d-bff4-928d601b0bc8

import Mathlib
import Definitions.Def_GroundTheory_IdeleRoots_TorusPowers_HeckeTensor
import Definitions.Def_GroundTheory_IdeleRoots_TorusPowers_HeckeIdem

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
variable {K : Type} [Field K] [NumberField K]
namespace GroundTheory.BlockD.ThmBHecke
theorem _root_.solution {w u : HeightOneSpectrum (𝓞 K)} (h : u ≠ w) : finSingleOne w u = 0 := by
  classical
  exact Pi.single_eq_of_ne (M := fun u : HeightOneSpectrum (𝓞 K) ↦ u.adicCompletion K) h 1
end GroundTheory.BlockD.ThmBHecke
