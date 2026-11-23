-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.RawDeg.res_pull_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:04.292795+00:00
-- url     : https://prove2.me/submissions/d94912ab-96cb-4825-b486-1274b346e7c1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_RawDegreeForms

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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings
variable (R : Type) [CommRing R] [IsDomain R]
attribute [instance] RawDeg.addCommGroup RawDeg.free RawDeg.finite
open GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.RawDeg
variable {R} (D : RawDeg R)
namespace GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.RawDeg
theorem _root_.solution {Y Z : Scheme.{0}} (f : Z ⟶ Y) {U V : Y.Opens} (h : V ≤ U) {W : Z.Opens}
    (k : W ≤ f ⁻¹ᵁ V) (k' : W ≤ f ⁻¹ᵁ U) (u : Γ(Y, U)ˣ) :
    res k (pullU f V (res h u)) = res k' (pullU f U u) := by
  ext
  simp only [res, pullU, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  change ((Y.presheaf.map (homOfLE h).op ≫ f.appLE V W k).hom _) = (f.appLE U W k').hom _
  rw [Scheme.Hom.map_appLE]
end GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.RawDeg
