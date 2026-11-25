-- Prove2me | solution 1 for GlobalTheory.ThetaSpecialise.isPull_pullOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:56:05.033711+00:00
-- url     : https://prove2.me/submissions/1d8f156c-3c90-47f5-86d9-a486993a3a31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsFOfIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfInjective
import Theorems.Thm_GlobalTheory_ThetaSpecialise_gs_pullOver


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaSpecialise
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar
  GlobalTheory.ThetaBaseChange
variable {X X' X'' Y Y' Y'' Y₁ Y₁' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {Φ : X' ⟶ X} {Φ' : X'' ⟶ X'}
  {K : Type} [Fintype K] {ε : K → ℤ}
namespace GlobalTheory.ThetaSpecialise
theorem _root_.solution {R R' : Type} [CommRing R] [CommRing R'] {φ : K → (Y ⟶ X)}
    {π : Y ⟶ Spec (CommRingCat.of R)} {π' : Y' ⟶ Spec (CommRingCat.of R')}
    {f : R →+* R'} {p : Y' ⟶ Y} (hp : p ≫ π = π' ≫ Spec.map (CommRingCat.ofHom f)) {φ' : K → (Y' ⟶ X)}
    (hφ : ∀ k, φ' k = p ≫ φ k) (s : SecOver π (LB.LinComb L φ ε)) : IsPull p (pullOver L ε hp hφ s) s := by
  unfold IsPull
  exact ⟨hφ, fun _ r z j hj => gs_pullOver hp hφ s r z j hj⟩
end GlobalTheory.ThetaSpecialise
