-- Prove2me | solution 1 for GlobalTheory.SS.Dil.gr_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:20.378865+00:00
-- url     : https://prove2.me/submissions/4fd03b92-67b1-476c-9ea6-05268be04a79

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
theorem _root_.solution (f : Fin n → MvPolynomial (Fin n) R) : gr σ (∑ j, f j) = ∑ j, gr σ (f j) := by
  funext i; simp [gr]
end GlobalTheory.SS.Dil
