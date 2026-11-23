-- Prove2me | solution 1 for GroundTheory.PAdicHodge.normTrace_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:34.158642+00:00
-- url     : https://prove2.me/submissions/042ac45f-6923-4524-937e-2d6856b33d68

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial Module IntermediateField
noncomputable section
variable (F : Type*) {Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
variable [CharZero F] [Algebra.IsIntegral F Ω]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → Ω) :
    normTrace F (∑ i ∈ s, f i) = ∑ i ∈ s, normTrace F (f i) :=
  map_sum (normTraceₗ F) f s
end GroundTheory.PAdicHodge
