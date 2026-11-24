-- Prove2me | solution 1 for GlobalTheory.AffineLineExt.isPrincipalIdealRing_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:55:31.097481+00:00
-- url     : https://prove2.me/submissions/34fef456-a1ab-4f5f-9254-9bb67beb662c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusToAbelianVarietyConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExtendAffineLineMorphismToProperAcrossPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AffineLineExt
open Polynomial
namespace GlobalTheory.AffineLineExt
theorem _root_.solution {R : Type} [CommRing R] [IsPrincipalIdealRing R] (r : R) :
    IsPrincipalIdealRing (Localization.Away r) := ⟨fun J => by
  rw [← IsLocalization.map_under (Submonoid.powers r) (Localization.Away r) J]
  obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal (J.under R)).principal
  rw [ha]
  exact ⟨⟨_, by rw [Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton]⟩⟩⟩
end GlobalTheory.AffineLineExt
