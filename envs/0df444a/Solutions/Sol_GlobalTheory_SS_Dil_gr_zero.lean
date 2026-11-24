-- Prove2me | solution 1 for GlobalTheory.SS.Dil.gr_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:16:42.76527+00:00
-- url     : https://prove2.me/submissions/247a235e-ad92-4292-9514-aa8b02850d20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnramifiedIdealLocusCharacterization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Dil
variable {R S : Type} {n : ℕ} [CommRing R] [CommRing S] (σ : MvPolynomial (Fin n) R →+* S)
namespace GlobalTheory.SS.Dil
theorem _root_.solution : gr σ 0 = 0 := by
  funext i; simp [gr]
end GlobalTheory.SS.Dil
