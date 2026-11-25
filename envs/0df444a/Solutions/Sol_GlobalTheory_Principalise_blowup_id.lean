-- Prove2me | solution 1 for GlobalTheory.Principalise.blowup_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:05:15.944733+00:00
-- url     : https://prove2.me/submissions/8db59de2-4065-4183-8f70-77de90b6f0ae

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
open GlobalTheory.Principalise
namespace GlobalTheory.Principalise
theorem _root_.solution {X : Scheme.{0}} {J : X.IdealSheafData} (h : FinalTheorems.EffCartier J) : FinalTheorems.Blowup (𝟙 X) J :=
  ⟨by rwa [Scheme.IdealSheafData.comap_id], fun _ g _ => ⟨g, Category.comp_id g, fun _ e => by simpa using e⟩⟩
end GlobalTheory.Principalise
