-- Prove2me | solution 1 for GroundTheory.Global.SemiLocal.tensorHomeomorph_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:17:32.235494+00:00
-- url     : https://prove2.me/submissions/87dbd082-e494-4686-a2f0-708227b55b8c

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Approximation
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_LocalDegree
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Finite

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
noncomputable section
open GroundTheory.Global.SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (L) (v : HeightOneSpectrum (𝓞 K))
namespace GroundTheory.Global.SemiLocal
theorem _root_.solution [TopologicalSpace (v.adicCompletion K ⊗[K] L)]
    [IsModuleTopology (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)]
    (y : v.adicCompletion K ⊗[K] L) : tensorHomeomorph L v y = tensorEquiv L v y := rfl
end GroundTheory.Global.SemiLocal
