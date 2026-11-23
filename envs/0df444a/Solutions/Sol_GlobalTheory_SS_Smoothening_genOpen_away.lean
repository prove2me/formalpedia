-- Prove2me | solution 1 for GlobalTheory.SS.Smoothening.genOpen_away
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:02:06.203636+00:00
-- url     : https://prove2.me/submissions/7b8195e2-c6c5-4dc1-9faf-e1c7b51e1fe5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DefectBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothOfDefectZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothFreeAwayStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnramifiedIdealLocusCharacterizationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SmoothFlatAlgebraFiniteCoverDecomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Smoothening
variable {R K B C D : Type} [CommRing R] [Field K] [Algebra R K] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
  [CommRing D] [Algebra R D]
namespace GlobalTheory.SS.Smoothening
theorem _root_.solution (f : B) : GenOpen K (IsScalarTower.toAlgHom R B (Localization.Away f)) := by
  unfold GenOpen
  letI : Algebra (K ⊗[R] B) (K ⊗[R] Localization.Away f) :=
    (Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom R B (Localization.Away f))).toRingHom.toAlgebra
  haveI : IsScalarTower K (K ⊗[R] B) (K ⊗[R] Localization.Away f) :=
    IsScalarTower.of_algHom (Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom R B (Localization.Away f)))
  have h := IsLocalization.tensorProduct_tensorProduct_right R K (Submonoid.powers f) (Localization.Away f) (by
    ext x; simp [RingHom.algebraMap_toAlgebra])
  rw [Submonoid.map_powers] at h
  exact IsOpenImmersion.of_isLocalization (R := CommRingCat.of (K ⊗[R] B)) (S := CommRingCat.of (K ⊗[R] Localization.Away f)) (Algebra.TensorProduct.includeRight (R := R) (A := K) f)
end GlobalTheory.SS.Smoothening
