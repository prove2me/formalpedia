-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Lat.mem_pullLoc_of_ctr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:36:08.003939+00:00
-- url     : https://prove2.me/submissions/2fa0645a-9836-4958-994e-74cf3fccce0c

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
theorem _root_.solution {L : Lat ξ E} {i : Ω →+* Ω'} (j : E →+ F) {p : Cpt ξ} {p' : Cpt ξ'}
    (h : IsCtrOf i p p') {e : E} (he : e ∈ L p) : j e ∈ L.pullLoc ξ' i j p' :=
  Submodule.subset_span ⟨p, h, e, he, rfl⟩
end Lat
end GlobalTheory.CompanionTheory.Ar
