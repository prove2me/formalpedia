-- Prove2me | solution 1 for GroundTheory.PAdicHodge.SpectralAlgClosure.norm_eq_spectralNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:18:18.34134+00:00
-- url     : https://prove2.me/submissions/8196a7ec-d9b9-4bd9-a4d1-3f55a8976a44

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_CompletedAlgClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable (K : Type*) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
open GroundTheory.PAdicHodge.SpectralAlgClosure
namespace GroundTheory.PAdicHodge.SpectralAlgClosure
theorem _root_.solution (x : SpectralAlgClosure K) :
    ‖x‖ = spectralNorm K (SpectralAlgClosure K) x :=
  rfl
end GroundTheory.PAdicHodge.SpectralAlgClosure
