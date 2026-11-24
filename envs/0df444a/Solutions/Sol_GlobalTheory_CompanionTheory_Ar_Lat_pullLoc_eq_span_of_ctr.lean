-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Lat.pullLoc_eq_span_of_ctr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:20:13.912378+00:00
-- url     : https://prove2.me/submissions/caf8502f-5608-486e-9a18-c4ee643c4379

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
theorem _root_.solution {L : Lat ξ E} {i : Ω →+* Ω'} (j : E →+ F) {p₀ : Cpt ξ} {p' : Cpt ξ'}
    (h : IsCtrOf i p₀ p') (hu : ∀ p : Cpt ξ, IsCtrOf i p p' → ∀ e ∈ L p, e ∈ L p₀) :
    L.pullLoc ξ' i j p' = Submodule.span (regAt ξ' p') (j '' (L p₀ : Set E)) := by
  refine congrArg _ (Set.ext fun e' => ⟨?_, ?_⟩)
  · rintro ⟨p, hp, e, he, rfl⟩
    exact ⟨e, hu p hp e he, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨p₀, h, e, he, rfl⟩
end Lat
end GlobalTheory.CompanionTheory.Ar
