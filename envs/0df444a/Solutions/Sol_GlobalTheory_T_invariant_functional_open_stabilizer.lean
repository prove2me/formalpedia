-- Prove2me | solution 1 for GlobalTheory.T.invariant_functional_open_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:00:06.590865+00:00
-- url     : https://prove2.me/submissions/a4cb89a3-d0b6-45fa-904d-d5811e87774b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvariantFunctionalOpenStabilizer
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvariantFunctionalOpenStabilizerStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Smooth_isOpen_linearForm_stabiliser


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
theorem _root_.solution : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G), IsOpen (K : Set G) → ∀ l : Module.Dual ℂ V, (∀ x ∈ K, l ∘ₗ ρ x = l) → IsOpen {g : G | l ∘ₗ ρ g = l} := by
  first | exact @GlobalTheory.CompanionTheory.Smooth.isOpen_linearForm_stabiliser | exact GlobalTheory.CompanionTheory.Smooth.isOpen_linearForm_stabiliser | (intros; apply GlobalTheory.CompanionTheory.Smooth.isOpen_linearForm_stabiliser <;> assumption)
end _root_.GlobalTheory.T
