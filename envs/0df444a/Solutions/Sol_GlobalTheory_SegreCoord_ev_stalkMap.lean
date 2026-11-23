-- Prove2me | solution 1 for GlobalTheory.SegreCoord.ev_stalkMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:20:42.329541+00:00
-- url     : https://prove2.me/submissions/99f14e46-ff97-46b5-8f06-55e8ed6ae057

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSegreCoordinates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.SegreCoord
variable {X : Scheme.{0}} {M : LB X} {σ : Type} {th : σ → M.Sec} {T T' : Type} [CommRing T] [CommRing T']
namespace GlobalTheory.SegreCoord
theorem _root_.solution (φ : T →+* T') (z : Sp T') (t : T) :
    ev z (φ t) = ((spMap φ).stalkMap z).hom (ev (spMap φ z) t) := by
  refine Eq.trans ?_ (Scheme.Hom.germ_stalkMap_apply (spMap φ) ⊤ z trivial _).symm
  have := congrArg (fun q => q.hom t) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  exact congrArg ((Sp T').presheaf.germ ⊤ z trivial).hom this
end GlobalTheory.SegreCoord
