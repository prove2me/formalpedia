-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PRep.JacExact.isOpen_stabIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:54:11.761398+00:00
-- url     : https://prove2.me/submissions/a6ac3f26-ca79-46fd-8892-4e432cda5d34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PRep GlobalTheory.CompanionTheory.PRep.JacExact
variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.CompanionTheory.PRep.JacExact
theorem _root_.solution [TopologicalSpace G] (τ : Representation ℂ G V) (hτ : IsSmooth τ)
    (L : Subgroup G) (x : V) : IsOpen (stabIn τ L x : Set L) :=
  (hτ x).preimage continuous_subtype_val
end GlobalTheory.CompanionTheory.PRep.JacExact
