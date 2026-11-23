-- Prove2me | solution 1 for GlobalTheory.ZH.ImmSep.valHom_constFn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:10:14.927593+00:00
-- url     : https://prove2.me/submissions/2333fd5b-2eeb-402f-bea2-568c8ca2dedf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnitCharts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_EqOfValHomEq

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
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.ImmSep
open GlobalTheory.ZH.CrdCalc
variable {R : Type} [CommRing R] {X : Scheme.{0}}
namespace GlobalTheory.ZH.ImmSep
theorem _root_.solution {k : Type} [CommRing k] (p : X ⟶ Sp k) (x : Sp R ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a : k) :
    valHom x U h (constFn p U a) = (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
      (((x ≫ p).appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a)) := by
  rw [← Scheme.Hom.appLE_comp_appLE x p ⊤ U ⊤ le_top h]
  rfl
end GlobalTheory.ZH.ImmSep
