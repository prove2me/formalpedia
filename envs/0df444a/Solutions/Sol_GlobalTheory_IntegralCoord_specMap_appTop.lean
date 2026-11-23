-- Prove2me | solution 1 for GlobalTheory.IntegralCoord.specMap_appTop
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:33.813087+00:00
-- url     : https://prove2.me/submissions/d2e2bc2c-a02c-4c30-b47c-03df10c9884e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsBasisOfEq

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IntegralCoord
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
namespace GlobalTheory.IntegralCoord
theorem _root_.solution {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (c : Γ(Spec (CommRingCat.of A), ⊤)) :
    (Spec.map (CommRingCat.ofHom f)).appTop.hom c =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (f ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom c)) := by
  have h2 := congrArg (fun φ => φ.hom c) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  rw [← h2]
  simp
end GlobalTheory.IntegralCoord
