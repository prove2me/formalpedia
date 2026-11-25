-- Prove2me | solution 1 for GlobalTheory.EigenLieCompare.exists_toCompletion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:54:03.432848+00:00
-- url     : https://prove2.me/submissions/c4a7dcbe-435a-47c7-acf6-9510c4e23ab5

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
import Theorems.Thm_GlobalTheory_SelfDualGenus_isAdicComplete_adicCompletionIntegers
import Theorems.Thm_GlobalTheory_SelfDualGenus_isUnit_algebraMap_iff
import Theorems.Thm_GlobalTheory_nonempty_padicInt_ringHom_of_isAdicComplete


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
variable {p : ℕ} [Fact p.Prime] {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.EigenLieCompare
theorem _root_.solution {w : HeightOneSpectrum (𝓞 E)} (hw : IsOver p w) :
    ∃ _ : Algebra ℤ_[p] (Ow w), True := by
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers w
  obtain ⟨φ⟩ := GlobalTheory.nonempty_padicInt_ringHom_of_isAdicComplete
    (IsLocalRing.maximalIdeal (Ow w)) p (by
      rw [← map_natCast (algebraMap (𝓞 E) (Ow w))]
      exact fun h => (GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff w _).1 h hw)
  exact ⟨φ.toAlgebra, trivial⟩
end GlobalTheory.EigenLieCompare
