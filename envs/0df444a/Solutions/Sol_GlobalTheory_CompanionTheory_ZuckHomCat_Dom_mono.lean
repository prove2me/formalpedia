-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckHomCat.Dom.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:52:05.727132+00:00
-- url     : https://prove2.me/submissions/312dc681-c80e-4f60-9e62-254b72026b1c

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HomCategory

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckHomCat
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData CompanionTheory.D.Upq.Sm
variable {k r : ℕ}
namespace GlobalTheory.CompanionTheory.ZuckHomCat
namespace Dom
theorem _root_.solution {X : Obj k r} {φ ψ : M X → ℝ} (h : Dom X ψ) (hle : ∀ x, φ x ≤ ψ x) : Dom X φ := by
  obtain ⟨C, Ws, hW, hb⟩ := h
  exact ⟨C, Ws, hW, fun x => (hle x).trans (hb x)⟩
end Dom
end GlobalTheory.CompanionTheory.ZuckHomCat
