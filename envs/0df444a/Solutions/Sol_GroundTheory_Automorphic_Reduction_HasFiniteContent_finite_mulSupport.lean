-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.HasFiniteContent.finite_mulSupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:11:57.074852+00:00
-- url     : https://prove2.me/submissions/45b55bba-1d30-4893-a1cc-e09a634da0dd

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
namespace GroundTheory.Automorphic.Reduction
namespace HasFiniteContent
theorem _root_.solution {y : Fin n → 𝔸[K]} (hy : HasFiniteContent y) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => ‖finComp v y‖).Finite :=
  Filter.eventually_cofinite.1 hy
end HasFiniteContent
end GroundTheory.Automorphic.Reduction
