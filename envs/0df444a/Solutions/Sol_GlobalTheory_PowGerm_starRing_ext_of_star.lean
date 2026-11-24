-- Prove2me | solution 1 for GlobalTheory.PowGerm.starRing_ext_of_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:28:18.603533+00:00
-- url     : https://prove2.me/submissions/cb32270c-6f10-41c8-a6a1-f1cfd9305080

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_StarRingExtOfStar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open GlobalTheory GlobalTheory.PowGerm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PowGerm
namespace _root_.GlobalTheory.PowGerm
theorem _root_.solution {R : Type*} [NonUnitalNonAssocSemiring R] (s t : StarRing R)
    (h : ∀ a : R, s.toStarMul.toInvolutiveStar.toStar.star a =
      t.toStarMul.toInvolutiveStar.toStar.star a) :
    s = t := by
  rcases s with @⟨@⟨@⟨@⟨s⟩, _⟩, _⟩, _⟩
  rcases t with @⟨@⟨@⟨@⟨t⟩, _⟩, _⟩, _⟩
  obtain rfl : s = t := funext h
  rfl
end _root_.GlobalTheory.PowGerm
end GlobalTheory.PowGerm
