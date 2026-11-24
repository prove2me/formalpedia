-- Prove2me | solution 1 for GlobalTheory.SS.OrdTwist.det_cross
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:20:36.283691+00:00
-- url     : https://prove2.me/submissions/933c1934-7b53-4edc-9586-f687f62335c7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AbelianVarietyAutomorphismShiftsJacobianOrder

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.OrdTwist
namespace GlobalTheory.SS.OrdTwist
theorem _root_.solution {K B : Type} [CommRing K] [CommRing B] [Algebra K B] {I : Type} [Fintype I] [DecidableEq I]
    (b : Module.Basis I B Ω[B⁄K]) (D D' : I → Derivation K B B) (t u : I → B) :
    (Matrix.of fun i j => D' i (t j)).det * (Matrix.of fun i j => D i (u j)).det =
      (Matrix.of fun i j => D' i (u j)).det * (Matrix.of fun i j => D i (t j)).det := by
  have key : ∀ (E : I → Derivation K B B) (v : I → B), (Matrix.of fun i j => E i (v j)).det =
      (Matrix.of fun i k => (E i).liftKaehlerDifferential (b k)).det *
        (Matrix.of fun k j => b.repr (KaehlerDifferential.D K B (v j)) k).det := by
    intro E v
    rw [← Matrix.det_mul]
    congr 1
    ext i j
    rw [Matrix.mul_apply, Matrix.of_apply, ← Derivation.liftKaehlerDifferential_comp_D (E i) (v j)]
    conv_lhs => rw [← b.sum_repr (KaehlerDifferential.D K B (v j))]
    simp only [map_sum, map_smul, smul_eq_mul, Matrix.of_apply, mul_comm]
  rw [key D' t, key D u, key D' u, key D t]
  ring
end GlobalTheory.SS.OrdTwist
