-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Smooth.isOpen_linearForm_stabiliser
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:39:43.492698+00:00
-- url     : https://prove2.me/submissions/c10e34a4-1cc4-4e86-b45f-4b29c541e1ec

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvariantFunctionalOpenStabilizer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Smooth
namespace GlobalTheory.CompanionTheory.Smooth
theorem _root_.solution {G V : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K : Subgroup G) (hK : IsOpen (K : Set G)) (l : Module.Dual ℂ V)
    (hl : ∀ x ∈ K, l ∘ₗ ρ x = l) : IsOpen {g : G | l ∘ₗ ρ g = l} :=
  Subgroup.isOpen_mono (H₁ := K) (H₂ := linearFormStabiliser ρ l) (fun x hx => hl x hx) hK
end GlobalTheory.CompanionTheory.Smooth
