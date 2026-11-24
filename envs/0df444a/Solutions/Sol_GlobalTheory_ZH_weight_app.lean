-- Prove2me | solution 1 for GlobalTheory.ZH.weight_app
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:17:53.631447+00:00
-- url     : https://prove2.me/submissions/e4098028-5edf-4e3f-8505-921c159714e2

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
    (h : V ≤ E.chart j) (χ : E.X) (a : Γ(E.B.left, V)) :
    D.weight j V hV h χ ((D.q.left.app V).hom a) = (Finsupp.single (0 : E.X) a) χ := by
  have e : (Equiv.ofBijective _ (D.coord j V hV h)).symm ((D.q.left.app V).hom a) =
      AddMonoidAlgebra.single 0 a := by
    rw [Equiv.symm_apply_eq, Equiv.ofBijective_apply]
    simp [AddMonoidAlgebra.liftNCRingHom]
  unfold SplitExt.GtDatum.weight
  rw [e, AddMonoidAlgebra.coeff_single]
end GlobalTheory.ZH
