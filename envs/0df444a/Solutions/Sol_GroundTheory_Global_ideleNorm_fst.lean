-- Prove2me | solution 1 for GroundTheory.Global.ideleNorm_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:12:43.7889+00:00
-- url     : https://prove2.me/submissions/de15d945-ee9a-45d6-af6a-280728a151ac

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_CompletionsOverBasisRepr
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_norm_adeleRing_fst

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
open scoped Classical
namespace GroundTheory.Global
theorem _root_.solution (x : IdeleGroup L) (v : InfinitePlace K) :
    ((ideleNorm K L x : IdeleGroup K) : 𝔸[K]).1 v =
      ∏ w : v.placesOver L, Algebra.norm v.Completion ((x : 𝔸[L]).1 w) :=
  norm_adeleRing_fst (K := K) v (x : 𝔸[L])
end GroundTheory.Global
