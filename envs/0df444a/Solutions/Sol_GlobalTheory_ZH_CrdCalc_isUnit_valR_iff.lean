-- Prove2me | solution 1 for GlobalTheory.ZH.CrdCalc.isUnit_valR_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:11:25.849981+00:00
-- url     : https://prove2.me/submissions/7dbfda89-f942-45ef-9218-4637154447c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnitCharts
import Theorems.Thm_GlobalTheory_ZH_CrdCalc_valR_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.CrdCalc
variable {R : Type} [CommRing R] {X : Scheme.{0}}
namespace GlobalTheory.ZH.CrdCalc
theorem _root_.solution (x : Sp R ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    IsUnit (valR x U f) ↔ ⊤ ≤ x ⁻¹ᵁ X.basicOpen f := by
  rw [valR_eq x U h]
  have e : IsUnit (valHom x U h f) ↔ IsUnit ((x.appLE U ⊤ h).hom f) :=
    isUnit_map_iff (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv _
  rw [e]
  have b := Scheme.basicOpen_appLE x ⊤ U h f
  constructor
  · intro hu
    rw [Scheme.basicOpen_of_isUnit _ hu] at b
    exact b.le.trans inf_le_right
  · intro hu
    rw [inf_eq_left.2 hu] at b
    refine RingedSpace.isUnit_of_isUnit_germ _ _ _ fun y hy => ?_
    exact (Scheme.mem_basicOpen _ _ y hy).1 (b.ge hy)
end GlobalTheory.ZH.CrdCalc
