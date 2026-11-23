-- Prove2me | solution 1 for GlobalTheory.ZH.CrdCalc.valR_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:11:25.925888+00:00
-- url     : https://prove2.me/submissions/e3599659-50cf-4d1c-9b5f-3b75f96bc1d9

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
theorem _root_.solution (x : Sp R ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f g : Γ(X, U)) :
    valR x U (f * g) = valR x U f * valR x U g := by
  simp only [valR_eq x U h, map_mul]
end GlobalTheory.ZH.CrdCalc
