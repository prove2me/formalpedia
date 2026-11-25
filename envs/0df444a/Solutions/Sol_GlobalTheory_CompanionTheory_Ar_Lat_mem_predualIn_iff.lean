-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Lat.mem_predualIn_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:36:03.387281+00:00
-- url     : https://prove2.me/submissions/988a8919-cd55-49bd-8ddd-05532d3857ad

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
theorem _root_.solution {L : Lat ξ (Module.Dual Ω E)} {V : Submodule Ω E} {p : Cpt ξ} {v : E} :
    v ∈ L.predualIn V p ↔ v ∈ V ∧ ∀ w ∈ L p, w v ∈ regAt ξ p := Iff.rfl
end Lat
end GlobalTheory.CompanionTheory.Ar
