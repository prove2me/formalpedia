-- Prove2me | solution 1 for GroundTheory.Global.SemiLocal.valued_algebraMap_int_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:00:04.009711+00:00
-- url     : https://prove2.me/submissions/255d1bf9-d399-402e-9d1a-5d03793a834d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_LocalDegree
import Theorems.Thm_GroundTheory_Global_SemiLocal_valued_algebraMap_int

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
open IsDedekindDomain NumberField WithZero
noncomputable section
open GroundTheory.Global.SemiLocal
variable {F : Type*} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))
namespace GroundTheory.Global.SemiLocal
theorem _root_.solution (b : 𝓞 F) :
    Valued.v (algebraMap (𝓞 F) (u.adicCompletion F) b) ≤ 1 := by
  rw [valued_algebraMap_int]
  exact u.intValuation_le_one b
end GroundTheory.Global.SemiLocal
