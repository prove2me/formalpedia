-- Prove2me | solution 1 for GlobalTheory.ZH.app_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:22:52.127576+00:00
-- url     : https://prove2.me/submissions/f31ca046-4305-42db-852b-77477c93fd39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_EqOfWeightEq

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
open GlobalTheory GlobalTheory.ZH
namespace GlobalTheory.ZH
theorem _root_.solution {X Y : Scheme.{0}} (q : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (h' : q ⁻¹ᵁ V ≤ q ⁻¹ᵁ U)
    (a : Γ(X, U)) :
    (q.app V).hom ((X.presheaf.map (homOfLE h).op).hom a) =
      (Y.presheaf.map (homOfLE h').op).hom ((q.app U).hom a) := by
  have := q.naturality (homOfLE h).op
  exact congrArg (fun f => f.hom a) this
end GlobalTheory.ZH
