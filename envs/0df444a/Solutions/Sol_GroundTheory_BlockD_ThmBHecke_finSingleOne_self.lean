-- Prove2me | solution 1 for GroundTheory.BlockD.ThmBHecke.finSingleOne_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:42:44.073128+00:00
-- url     : https://prove2.me/submissions/8dbdc026-4afa-4132-9b50-2e4a06fc2a0a

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
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) : finSingleOne w w = 1 := by
  classical
  exact Pi.single_eq_same (M := fun u : HeightOneSpectrum (𝓞 K) ↦ u.adicCompletion K) w 1
end GroundTheory.BlockD.ThmBHecke
