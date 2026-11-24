-- Prove2me | solution 1 for GlobalTheory.T.induced_representation_character
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:14:55.287102+00:00
-- url     : https://prove2.me/submissions/486ba100-dcd4-4960-b463-8c7994433d9b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InducedRepresentationCharacter
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__BrauerDegreeZero_fefd58e19a2fa426
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InducedRepresentationCharacterStatement
import Theorems.Thm_GlobalTheory_InertiaEigenvalues_inducedRep_cyclic_trace


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Published
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G : Type) [Group G] [Fintype G] (H : Subgroup G) (χ : H →* ℂˣ), ∃ (R : Representation ℂ G (Fin H.index → ℂ)) (v : Fin H.index → ℂ), (∀ σ : H, R σ v = (χ σ : ℂ) • v) ∧ Submodule.span ℂ (Set.range fun g => R g v) = ⊤ ∧ ∀ g, LinearMap.trace ℂ (Fin H.index → ℂ) (R g) = indFun H (fun x => (χ x : ℂ)) g := by
  first | exact @GlobalTheory.InertiaEigenvalues.inducedRep_cyclic_trace | exact GlobalTheory.InertiaEigenvalues.inducedRep_cyclic_trace | (intros; apply GlobalTheory.InertiaEigenvalues.inducedRep_cyclic_trace <;> assumption)
end _root_.GlobalTheory.T
