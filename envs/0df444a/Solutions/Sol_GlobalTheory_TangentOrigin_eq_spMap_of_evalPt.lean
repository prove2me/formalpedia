-- Prove2me | solution 1 for GlobalTheory.TangentOrigin.eq_spMap_of_evalPt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:56:19.242866+00:00
-- url     : https://prove2.me/submissions/36c78332-5be6-4038-a047-812e520c869c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Theorems.Thm_GlobalTheory_TangentOrigin_ext_evalPt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.TangentOrigin
variable {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
namespace GlobalTheory.TangentOrigin
theorem _root_.solution {k : Type} [CommRing k] (y : Sp R ⟶ Sp k) (φ : k →+* R)
    (h : ∀ a, evalPt y ⊤ le_rfl ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a) = φ a) :
    y = spMap φ := by
  refine ext_evalPt (isAffineOpen_top _) le_rfl le_rfl (RingHom.ext fun b => ?_)
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2 b
  exact (h a).trans (evalPt_spMap φ a).symm
end GlobalTheory.TangentOrigin
