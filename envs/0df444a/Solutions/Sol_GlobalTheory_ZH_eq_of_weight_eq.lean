-- Prove2me | solution 1 for GlobalTheory.ZH.eq_of_weight_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:22:06.170843+00:00
-- url     : https://prove2.me/submissions/f56cea60-2c4a-4556-9502-2a738e28c48a

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
theorem _root_.solution {S : Scheme.{0}} {E : SplitExt S} {G : Over S} [GrpObj G]
    (D : E.GtDatum G) (j : E.ChartIdx) (V : E.B.left.Opens) (hV : IsAffineOpen V)
    (h : V ≤ E.chart j) {s s' : Γ(G.left, D.q.left ⁻¹ᵁ V)}
    (e : ∀ χ, D.weight j V hV h χ s = D.weight j V hV h χ s') : s = s' := by
  apply (Equiv.ofBijective _ (D.coord j V hV h)).symm.injective
  apply AddMonoidAlgebra.ext
  ext χ
  exact e χ
end GlobalTheory.ZH
