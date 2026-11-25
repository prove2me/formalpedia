-- Prove2me | solution 1 for GroundTheory.PAdicHodge.algebraMap_intermediateField_cp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:22:23.253587+00:00
-- url     : https://prove2.me/submissions/80078b25-4937-49ca-931f-46f5b08d8938

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_TateCpTwist

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
open UniformSpace
variable {p : ℕ} [Fact p.Prime]
variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))
namespace GroundTheory.PAdicHodge
theorem _root_.solution (k : K) :
    algebraMap K ℂ_[p] k = ((k : PadicAlgCl p) : ℂ_[p]) := rfl
end GroundTheory.PAdicHodge
