-- Prove2me | solution 1 for GlobalTheory.T.exists_representatives_two_element_orbits_involution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:10:08.872464+00:00
-- url     : https://prove2.me/submissions/90db97fb-ae01-4a38-b546-60e4a7827a7c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsRepresentativesTwoElementOrbitsInvolution
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsRepresentativesTwoElementOrbitsInvolutionStatement
import Theorems.Thm_GlobalTheory_involution_pair_representatives


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (ι : Type) [Finite ι] (s : ι → ι), (∀ i, s (s i) = i) → ∃ (r : ℕ) (e : Fin r → ι), (∀ j k, e j = e k → j = k) ∧ (∀ j k, s (e j) ≠ e k) ∧ ∀ i, s i = i ∨ ∃ j, i = e j ∨ i = s (e j) := by
  first | exact @GlobalTheory.involution_pair_representatives | exact GlobalTheory.involution_pair_representatives | (intros; apply GlobalTheory.involution_pair_representatives <;> assumption)
end _root_.GlobalTheory.T
