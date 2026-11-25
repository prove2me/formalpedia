-- Prove2me | solution 1 for GlobalTheory.LogKS.coe_interior
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:05:19.052826+00:00
-- url     : https://prove2.me/submissions/8ebefd62-a6ca-457b-815f-4134e8fc3fdf

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
theorem _root_.solution : (interior Y : Set Y.X) = abLocus Y.t.G := by
  have := isIso_fst Y
  have hs : Function.Surjective (pullback.fst Y.s (spMap (RingHom.id c.F))) :=
    (pullback.fst Y.s (spMap (RingHom.id c.F))).surjective
  rw [← Set.image_preimage_eq (abLocus Y.t.G) hs, Y.ab_gen, ← Set.range_comp]
  rfl
end GlobalTheory.LogKS
