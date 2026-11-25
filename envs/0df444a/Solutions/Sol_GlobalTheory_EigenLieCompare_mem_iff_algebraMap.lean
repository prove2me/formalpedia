-- Prove2me | solution 1 for GlobalTheory.EigenLieCompare.mem_iff_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:02:49.569189+00:00
-- url     : https://prove2.me/submissions/d820ba77-edc0-412e-9bf1-deff0f6a52ec

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
import Theorems.Thm_GlobalTheory_SelfDualGenus_isUnit_algebraMap_iff


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
theorem _root_.solution (w : HeightOneSpectrum (𝓞 E)) (a : 𝓞 E) :
    a ∈ w.asIdeal ↔ algebraMap (𝓞 E) (Ow w) a ∈ IsLocalRing.maximalIdeal (Ow w) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff,
    not_not]
end GlobalTheory.EigenLieCompare
