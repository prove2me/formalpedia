-- Prove2me | solution 1 for GlobalTheory.LeadingMinorInv.mul_flagMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:34:41.055285+00:00
-- url     : https://prove2.me/submissions/1dc1dac7-ac93-474e-a68b-22d409d218e0

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingMinorInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.LeadingMinorInv
open Formalism.QuantumDeterminants
namespace GlobalTheory.LeadingMinorInv
theorem _root_.solution (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i) (b) :
    (g * flagMat k r z) i b = (g *ᵥ fvec k r z b) i := rfl
end GlobalTheory.LeadingMinorInv
