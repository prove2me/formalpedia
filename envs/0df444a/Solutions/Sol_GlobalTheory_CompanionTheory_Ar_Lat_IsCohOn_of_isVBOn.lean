-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Lat.IsCohOn.of_isVBOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:40:25.337992+00:00
-- url     : https://prove2.me/submissions/8d0b1435-243b-4e21-bcf6-3f6f8d7259de

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
namespace Lat.IsCohOn
theorem _root_.solution {L : Lat ξ E} {T : Set (Cpt ξ)} {r : ℕ} {V : Submodule Ω E} (h : L.IsVBOn T r V) :
    L.IsCohOn T := fun p hp => by
  obtain ⟨U, hU, b, -, hb⟩ := h p hp
  exact ⟨U, hU, r, b, fun q hq hqU => (hb q hq hqU).2⟩
end Lat.IsCohOn
end GlobalTheory.CompanionTheory.Ar
