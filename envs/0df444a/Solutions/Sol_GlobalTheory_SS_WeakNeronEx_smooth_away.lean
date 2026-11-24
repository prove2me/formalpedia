-- Prove2me | solution 1 for GlobalTheory.SS.WeakNeronEx.smooth_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:42:44.500805+00:00
-- url     : https://prove2.me/submissions/63c594aa-a8ca-43ee-b816-35041cd35d7b

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
import Theorems.Thm_GlobalTheory_SS_WeakNeronEx_away_of_irreducible
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
namespace GlobalTheory.SS.WeakNeronEx
theorem _root_.solution {π : R} (hπ : Irreducible π) (B : Type) [CommRing B] [Algebra R B]
    [Algebra.Smooth K (TensorProduct R K B)] : Algebra.Smooth R (Localization.Away (algebraMap R B π)) := by
  have := away_of_irreducible R K hπ
  have h₁ : Algebra.Smooth R K := Algebra.Smooth.of_isLocalization_Away π
  have h₂ : Algebra.Smooth R (TensorProduct R K B) := Algebra.Smooth.comp R K _
  letI : Algebra B (TensorProduct R K B) := Algebra.TensorProduct.rightAlgebra
  have hl : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers π)) (TensorProduct R K B) :=
    IsLocalization.tensorRight K (Submonoid.powers π)
  rw [Algebra.algebraMapSubmonoid_powers] at hl
  haveI : IsScalarTower R B (TensorProduct R K B) := Algebra.TensorProduct.right_isScalarTower
  exact Algebra.Smooth.of_equiv ((IsLocalization.algEquiv (Submonoid.powers (algebraMap R B π))
    (TensorProduct R K B) (Localization.Away (algebraMap R B π))).restrictScalars R)
end GlobalTheory.SS.WeakNeronEx
