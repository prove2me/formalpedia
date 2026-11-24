-- Prove2me | solution 1 for GlobalTheory.SS.Dil.gr_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:16:42.027052+00:00
-- url     : https://prove2.me/submissions/7f8a46ce-4dfb-4fb3-a7af-e79fc32fe8b8

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
theorem _root_.solution (j) : gr σ (X j) = Pi.single j 1 := by
  funext i
  by_cases h : i = j
  · subst h; simp [gr]
  · simp [gr, pderiv_X_of_ne (Ne.symm h), h]
end GlobalTheory.SS.Dil
