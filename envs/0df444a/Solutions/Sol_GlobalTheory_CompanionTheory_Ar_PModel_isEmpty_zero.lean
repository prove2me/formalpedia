-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PModel.isEmpty_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:33:54.224551+00:00
-- url     : https://prove2.me/submissions/a935621f-54a6-4cf3-8957-dc17b6d88c06

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsGenOfIsVBOne
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_StalkClosedPointToToStalk
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_GlueApplyOfNotInFibre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open AlgebraicGeometry CategoryTheory
namespace GlobalTheory.CompanionTheory.Ar
namespace PModel
theorem _root_.solution (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) :
    IsEmpty (PModel o (0 : κ → Ω)) :=
  ⟨fun M => by
    obtain ⟨c, hc⟩ := M.tie.cover (CptModel.self M.ξ)
    exact hc.1 rfl⟩
end PModel
end GlobalTheory.CompanionTheory.Ar
