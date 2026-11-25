-- Prove2me | solution 1 for GlobalTheory.LogKS.dense_interior
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:05:23.349342+00:00
-- url     : https://prove2.me/submissions/d63ad12d-af76-429f-9cd8-0f698c396246

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsChartIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__DenseInterior_23def473f6482931

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped Matrix
open GlobalTheory GlobalTheory.LogKS
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F))
namespace GlobalTheory.LogKS
theorem _root_.solution : Dense (interior Y : Set Y.X) := by
  have := isIso_fst Y
  have hs : Function.Surjective (pullback.fst Y.s (spMap (RingHom.id c.F))) :=
    (pullback.fst Y.s (spMap (RingHom.id c.F))).surjective
  exact hs.denseRange.comp Y.jQ_dense (pullback.fst Y.s (spMap (RingHom.id c.F))).continuous
end GlobalTheory.LogKS
