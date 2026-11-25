-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Lat.glue_apply_of_not_inFibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:35:59.982318+00:00
-- url     : https://prove2.me/submissions/2d703c7e-1f5e-4cb7-8636-6c166dd8305d

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
theorem _root_.solution {S : Finset ℕ} (L₀ : Lat ξ E) (Lq : ℕ → Lat ξ E) {p : Cpt ξ}
    (hp : ∀ q ∈ S, ¬ InFibre ξ q p) : Lat.glue S L₀ Lq p = L₀ p :=
  dif_neg fun ⟨q, hq, h⟩ => hp q hq h
end Lat
end GlobalTheory.CompanionTheory.Ar
