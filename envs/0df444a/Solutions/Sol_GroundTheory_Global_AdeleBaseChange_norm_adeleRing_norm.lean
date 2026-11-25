-- Prove2me | solution 1 for GroundTheory.Global.AdeleBaseChange.norm_adeleRing_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:05:19.671837+00:00
-- url     : https://prove2.me/submissions/b770dcd6-dcfe-40bd-aac4-f6e1060193d8

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_InfiniteAdeleRingMapInfiniteAdeleRingMap

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
open IsDedekindDomain NumberField
open scoped NumberField.AdeleRing NumberField.LiesOver
noncomputable section
open GroundTheory.Global.AdeleBaseChange
open SemiLocal
variable {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
namespace GroundTheory.Global.AdeleBaseChange
theorem _root_.solution (y : 𝔸[M]) :
    Algebra.norm 𝔸[K] (Algebra.norm 𝔸[L] y) = Algebra.norm 𝔸[K] y :=
  Algebra.norm_norm
end GroundTheory.Global.AdeleBaseChange
