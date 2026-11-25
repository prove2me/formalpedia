-- Prove2me | solution 1 for GlobalTheory.ThetaSpecialise.eq_pullOver_of_secScal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:07:15.425683+00:00
-- url     : https://prove2.me/submissions/34204d1f-924c-41d3-b5ed-64e278b0cba6

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
import Theorems.Thm_GlobalTheory_ThetaSpecialise_secScal_one_iff
import Theorems.Thm_GlobalTheory_FieldBaseChange_sval_pullOver
import Theorems.Thm_P2M_GlobalTheory_FieldBaseChange_sec_ext__7d36e2669680


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
variable {φ : K → (Y ⟶ X)} {φ₁ : K → (Y₁ ⟶ X)} {φ₂ : K → (Y₁' ⟶ X)} {a : Y₁ ⟶ Y} {b : Y₁' ⟶ Y₁}
  {s : LB.Sec (LB.LinComb L φ ε)} {t : LB.Sec (LB.LinComb L φ₁ ε)} {v : LB.Sec (LB.LinComb L φ₂ ε)}
namespace GlobalTheory.ThetaSpecialise
theorem _root_.solution (hL : L.IsLB) {R R' : Type} [CommRing R] [CommRing R']
    {π : Y ⟶ Spec (CommRingCat.of R)} {π' : Y₁ ⟶ Spec (CommRingCat.of R')}
    {f : R →+* R'} (hp : a ≫ π = π' ≫ Spec.map (CommRingCat.ofHom f)) (hφ : ∀ k, φ₁ k = a ≫ φ k)
    (h : GeneratorPullback.SecScal L φ₁ ε t φ ε s a 1) : pullOver L ε hp hφ s = t := by
  apply sec_ext' hL
  intro y J hJ
  rw [sval_pullOver hp hφ s (𝟙 Y₁) hJ]
  exact (secScal_one_iff hL).1 h y J hJ
end GlobalTheory.ThetaSpecialise
