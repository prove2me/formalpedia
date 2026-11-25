-- Prove2me | solution 1 for GlobalTheory.IsSmoothBlowupSeq.single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:03:34.989799+00:00
-- url     : https://prove2.me/submissions/ad9eec87-4e63-450b-818c-3eba2b70342b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory
namespace GlobalTheory
namespace IsSmoothBlowupSeq
theorem _root_.solution {S Y Y' : Scheme.{0}} {f : Y ⟶ S} {B : Set Y} (J : Y.IdealSheafData) (π : Y' ⟶ Y)
    (h₁ : Smooth (J.subschemeι ≫ f)) (h₂ : (J.support : Set Y) ⊆ B) (h₃ : FinalTheorems.Blowup π J) :
    IsSmoothBlowupSeq f B π := by
  simpa using IsSmoothBlowupSeq.step (f := f) (B := B) J π .id (by simpa using h₁) (by simpa using h₂) h₃
end IsSmoothBlowupSeq
end GlobalTheory
