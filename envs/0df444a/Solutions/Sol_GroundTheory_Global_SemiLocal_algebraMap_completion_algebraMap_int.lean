-- Prove2me | solution 1 for GroundTheory.Global.SemiLocal.algebraMap_completion_algebraMap_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:15:23.319368+00:00
-- url     : https://prove2.me/submissions/f12b111d-82cd-48af-976c-8874535305d4

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_LocalDegree
import Theorems.Thm_GroundTheory_Global_SemiLocal_algebraMap_completion_eq


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
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]
namespace GroundTheory.Global.SemiLocal
theorem _root_.solution (r : 𝓞 K) :
    algebraMap (v.adicCompletion K) (w.adicCompletion L) (algebraMap (𝓞 K) _ r) =
      algebraMap (𝓞 L) (w.adicCompletion L) (algebraMap (𝓞 K) (𝓞 L) r) := by
  rw [IsScalarTower.algebraMap_apply (𝓞 K) K (v.adicCompletion K), algebraMap_completion_eq,
    completionMap_algebraMap, IsScalarTower.algebraMap_apply K L (w.adicCompletion L),
    IsScalarTower.algebraMap_apply (𝓞 L) L (w.adicCompletion L),
    ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L, ← IsScalarTower.algebraMap_apply (𝓞 K) K L]
end GroundTheory.Global.SemiLocal
