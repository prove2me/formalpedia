-- Prove2me | solution 1 for GlobalTheory.SS.WeakNeronEx.flat_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:21:41.961321+00:00
-- url     : https://prove2.me/submissions/43fe010a-1f10-4a3e-a7ae-201a1c40bb8d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SmoothFlatAlgebraFiniteCoverDecompStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSchemeModelOfAffineSmoothChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCoverModelIrreducibleSpecialFibreStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsWeakNeronModel

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
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.WeakNeronEx
open GlobalTheory.AbLaw ReciprocityTheory.ChartRestriction.G.Out
variable (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  {D : Type} [CommRing D] [Algebra K D] [Algebra R D] [IsScalarTower R K D]
include K
namespace GlobalTheory.SS.WeakNeronEx
theorem _root_.solution (B : Subalgebra R D) : Module.Flat R B := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, Submodule.eq_bot_iff]
  rintro x ⟨c, hc⟩
  have hu : IsUnit (algebraMap R D c) := by
    rw [IsScalarTower.algebraMap_apply R K D]
    exact (IsLocalization.map_units K c).map _
  have : algebraMap R D c * (x : D) = 0 := by
    rw [← Algebra.smul_def]
    exact congrArg Subtype.val hc
  exact Subtype.ext (hu.mul_right_eq_zero.1 this)
end GlobalTheory.SS.WeakNeronEx
