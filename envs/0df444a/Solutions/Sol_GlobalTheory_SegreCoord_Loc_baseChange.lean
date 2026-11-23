-- Prove2me | solution 1 for GlobalTheory.SegreCoord.Loc.baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:28:21.957823+00:00
-- url     : https://prove2.me/submissions/a7945fc8-817a-4910-a8ad-79b9edc4b005

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
import Theorems.Thm_GlobalTheory_SegreCoord_gs_stalkMap
import Theorems.Thm_GlobalTheory_SegreCoord_ev_stalkMap

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
namespace Loc
theorem _root_.solution {x : Sp T ⟶ X} {v : σ → T} (h : Loc M th x v) (φ : T →+* T') :
    Loc M th (spMap φ ≫ x) (fun i => φ (v i)) := fun z j hz => by
  obtain ⟨u, hu⟩ := h (spMap φ z) j hz
  refine ⟨Units.map ((spMap φ).stalkMap z).hom.toMonoidHom u, fun i => ?_⟩
  rw [gs_stalkMap _ x z _ hz, hu, map_mul, ev_stalkMap]; rfl
end Loc
end GlobalTheory.SegreCoord
