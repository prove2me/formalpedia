-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Lat.pullLoc_eq_bot_of_no_ctr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:37:38.046945+00:00
-- url     : https://prove2.me/submissions/41be62cf-b3d6-44cc-9b55-235dc2e052ba

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
theorem _root_.solution (L : Lat ξ E) {i : Ω →+* Ω'} (j : E →+ F) {p' : Cpt ξ'}
    (h : ∀ p : Cpt ξ, ¬ IsCtrOf i p p') : L.pullLoc ξ' i j p' = ⊥ :=
  Submodule.span_eq_bot.2 fun _ ⟨p, hp, _⟩ => (h p hp).elim
end Lat
end GlobalTheory.CompanionTheory.Ar
