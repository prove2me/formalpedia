-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PRep.JacExact.avg_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:36:24.107558+00:00
-- url     : https://prove2.me/submissions/5d58a7d4-b63e-4fe3-9a5b-901ec44b7d38

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
variable {L V W : Type} [Group L] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.CompanionTheory.PRep.JacExact
theorem _root_.solution (τ : Representation ℂ L V) (χ : L →* ℂˣ) (M : Subgroup L) [Fintype (L ⧸ M)] (x : V) :
    avg τ χ M x = ∑ q : L ⧸ M, (((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ) • τ (Quotient.out q) x := by
  simp [avg, LinearMap.sum_apply]
end GlobalTheory.CompanionTheory.PRep.JacExact
