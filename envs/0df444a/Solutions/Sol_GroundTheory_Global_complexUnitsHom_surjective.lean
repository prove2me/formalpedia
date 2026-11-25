-- Prove2me | solution 1 for GroundTheory.Global.complexUnitsHom_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:07:42.349582+00:00
-- url     : https://prove2.me/submissions/cd0827ea-8ab5-44a3-a075-cfb50c73f142

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnitary
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain Function Complex
open scoped NumberField.AdeleRing
open GroundTheory GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open NumberField.InfinitePlace.Completion
omit [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution {w : InfinitePlace K} (hw : w.IsComplex) (a : (w.Completion)ˣ) :
    complexUnitsHom hw
      (Units.map (ringEquivComplexOfIsComplex hw : w.Completion →+* ℂ).toMonoidHom a) = a :=
  Units.ext ((ringEquivComplexOfIsComplex hw).symm_apply_apply _)
end GroundTheory.Global
