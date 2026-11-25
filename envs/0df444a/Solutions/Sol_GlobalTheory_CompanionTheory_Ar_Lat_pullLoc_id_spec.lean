-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Lat.pullLoc_id_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:37:44.409735+00:00
-- url     : https://prove2.me/submissions/fd9a3b23-14cc-42fa-a51a-0613f11b998e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsGenOfIsVBOne
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_StalkClosedPointToToStalk
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_GlueApplyOfNotInFibre
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Lat_pullLoc_eq_span_of_ctr

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
theorem _root_.solution {R : Type} [CommRing R] {φ : R →+* Ω} (hφ : Function.Injective φ)
    (L : Lat (CptModel.pt φ) E) : L.pullLoc (CptModel.pt φ) (RingHom.id Ω) (AddMonoidHom.id E) = L := by
  funext p
  rw [Lat.pullLoc_eq_span_of_ctr _ (IsCtrOf.refl p) fun q hq e he => by
    rwa [← IsCtrOf.unique_spec hφ hq (IsCtrOf.refl p)]]
  simp
end Lat
end GlobalTheory.CompanionTheory.Ar
