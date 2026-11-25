-- Prove2me | solution 1 for GroundTheory.Global.coe_mem_localIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:41:55.087069+00:00
-- url     : https://prove2.me/submissions/4dde04d8-bfa8-474c-a5cf-423362168ab5

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_IdeleAction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped NumberField.AdeleRing nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution {I : FractionalIdeal (𝓞 K)⁰ K} (v : HeightOneSpectrum (𝓞 K)) {x : K}
    (hx : x ∈ I) : (x : v.adicCompletion K) ∈ localIdeal I v :=
  Submodule.subset_span ⟨x, hx, rfl⟩
end GroundTheory.Global
