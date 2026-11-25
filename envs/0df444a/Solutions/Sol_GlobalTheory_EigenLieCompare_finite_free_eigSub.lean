-- Prove2me | solution 1 for GlobalTheory.EigenLieCompare.finite_free_eigSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:54:40.335141+00:00
-- url     : https://prove2.me/submissions/aae586c8-2669-4e55-890c-8652a53516e2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StAvDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_ConjugatePlaceEigen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CotangentBidualToTangentFunctionInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NonemptyPadicIntRingHomOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsTorusAndQuotientHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MulEqZeroOfToCompletion
import Theorems.Thm_GlobalTheory_HodgeTateCompare_finite_projective_of_smooth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open GlobalTheory GlobalTheory.EigenLieCompare
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen GlobalTheory.HodgeTateCompare
open GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems (Lie Cotangent)
variable {O : Type} [CommRing O] [IsDomain O] [ValuationRing O]
  {G : Over (Spec (CommRingCat.of O))} [GrpObj G]
  [IsCommMonObj G] {R : Type} [CommRing R] (α : RingAct G R)
variable [Smooth G.hom]
namespace GlobalTheory.EigenLieCompare
theorem _root_.solution (τ : R →+* O) :
    Module.Finite O (eigSub α τ) ∧ Module.Free O (eigSub α τ) := by
  obtain ⟨h₁, h₂⟩ := finite_projective_of_smooth (G := G)
  obtain ⟨r, hr⟩ := exists_retraction_eigSub α τ
  haveI : Module.Finite O (eigSub α τ) :=
    Module.Finite.of_surjective r fun x => ⟨x.1, LinearMap.congr_fun hr x⟩
  haveI : Module.Projective O (eigSub α τ) := Module.Projective.of_split _ r hr
  exact ⟨inferInstance, Module.free_of_flat_of_isLocalRing⟩
end GlobalTheory.EigenLieCompare
