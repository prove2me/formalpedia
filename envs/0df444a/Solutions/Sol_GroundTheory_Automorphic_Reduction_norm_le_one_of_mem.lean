-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.norm_le_one_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:21:45.835001+00:00
-- url     : https://prove2.me/submissions/faa812fa-04a1-47de-978f-3ca1b69a349b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicGLn
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
variable (v : HeightOneSpectrum (𝓞 K))
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution {x : v.adicCompletion K} (hx : x ∈ v.adicCompletionIntegers K) :
    ‖x‖ ≤ 1 :=
  (Valued.toNormedField.norm_le_one_iff).2
    ((HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) K v).1 hx)
end GroundTheory.Automorphic.Reduction
