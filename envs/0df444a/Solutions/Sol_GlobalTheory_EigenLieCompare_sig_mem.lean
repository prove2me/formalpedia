-- Prove2me | solution 1 for GlobalTheory.EigenLieCompare.sig_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:01:09.539799+00:00
-- url     : https://prove2.me/submissions/e7b74432-ecd5-4c77-96ac-cdc97e951fe9

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
import Theorems.Thm_GlobalTheory_EigenLieCompare_toPadic_apply
import Theorems.Thm_GlobalTheory_EigenLieCompare_sig_tmul

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
variable {p : ℕ} [Fact p.Prime] {E : Type} [Field E] [NumberField E] [IsCMField E]
variable [StarRing (𝓞 E)] (hs : ∀ a : 𝓞 E, star a = conjInt E a)
include hs
namespace GlobalTheory.EigenLieCompare
theorem _root_.solution {w : HeightOneSpectrum (𝓞 E)} {x : PadicOrder p E} (hx : x ∈ plId p w) :
    sig p (𝓞 E) x ∈ plId p (conjPlace w) := by
  have : plId p w ≤ (plId p (conjPlace w)).comap (sig p (𝓞 E)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, toPadic_apply, sig_tmul hs]
    refine Ideal.mem_map_of_mem (toPadic p E) ?_
    change conjInt E (conjInt E a) ∈ w.asIdeal
    rwa [conjInt_conjInt]
  exact this hx
end GlobalTheory.EigenLieCompare
