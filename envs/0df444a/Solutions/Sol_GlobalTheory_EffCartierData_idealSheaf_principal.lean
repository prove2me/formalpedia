-- Prove2me | solution 1 for GlobalTheory.EffCartierData.idealSheaf_principal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:40:44.03211+00:00
-- url     : https://prove2.me/submissions/9293be82-2a65-4bc4-bf4c-3ab0c4758ce8

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open Cartier
open GlobalTheory.EffCartierData
variable {X Y Z : Scheme.{0}}
variable (D D' : EffCartierData X)
namespace GlobalTheory.EffCartierData
theorem _root_.solution (a : Γ(X, ⊤)) (ha : IsRegularFn a) :
    (principal a ha).idealSheaf = Scheme.IdealSheafData.ofIdealTop (Ideal.span {a}) := by
  ext W : 2
  rw [(principal a ha).ideal_idealSheaf W ⟨⟩ le_top, Scheme.IdealSheafData.ofIdealTop_ideal,
    Ideal.map_span, Set.image_singleton]
  rfl
end GlobalTheory.EffCartierData
