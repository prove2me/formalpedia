-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Lat.pullLoc_congr_ctr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:40:31.893121+00:00
-- url     : https://prove2.me/submissions/283ee052-7f70-43bd-9eb8-0c0b0f448b32

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
variable {X X' X'' : Scheme.{0}} {Ω Ω' Ω'' : Type} [Field Ω] [Field Ω'] [Field Ω'']
  {E F : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup F] [Module Ω' F]
variable {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'}
  {ξ'' : Spec (CommRingCat.of Ω'') ⟶ X''}
namespace GlobalTheory.CompanionTheory.Ar
namespace Lat
theorem _root_.solution {L L' : Lat ξ E} {i : Ω →+* Ω'} (j : E →+ F) {p' : Cpt ξ'}
    (h : ∀ p : Cpt ξ, IsCtrOf i p p' → L p = L' p) : L.pullLoc ξ' i j p' = L'.pullLoc ξ' i j p' := by
  refine congrArg _ (Set.ext fun e' => exists_congr fun p => and_congr_right fun hp => ?_)
  rw [h p hp]
end Lat
end GlobalTheory.CompanionTheory.Ar
