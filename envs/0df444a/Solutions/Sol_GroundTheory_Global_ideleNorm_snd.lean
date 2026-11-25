-- Prove2me | solution 1 for GroundTheory.Global.ideleNorm_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:07:13.805021+00:00
-- url     : https://prove2.me/submissions/a06a9086-47a8-4175-bbae-1ba4d5b0206a

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_CompletionsOverBasisRepr
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_norm_adeleRing_snd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField TensorProduct Module
open scoped NumberField.AdeleRing NumberField.LiesOver
noncomputable section
open AdeleBaseChange SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
namespace GroundTheory.Global
theorem _root_.solution (x : IdeleGroup L) (v : HeightOneSpectrum (𝓞 K)) :
    ((ideleNorm K L x : IdeleGroup K) : 𝔸[K]).2 v =
      ∏ w : PlacesOver L v, Algebra.norm (v.adicCompletion K) ((x : 𝔸[L]).2 w.1) :=
  norm_adeleRing_snd (K := K) v (x : 𝔸[L])
end GroundTheory.Global
