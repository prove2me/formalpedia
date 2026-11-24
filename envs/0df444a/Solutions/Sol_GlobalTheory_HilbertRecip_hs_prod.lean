-- Prove2me | solution 1 for GlobalTheory.HilbertRecip.hs_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:34:12.206005+00:00
-- url     : https://prove2.me/submissions/27dd60c5-5440-4291-9987-9eaaba9eb977

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSquareMulInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AlmostNormFinDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsApproxModLocalSquares
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsLocalNonnormOfNonsquareAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexSquaresSUnitsNumberField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitValuationEqOfAdm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsAdmissibleSupersetFinitePlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSupersetMemSUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsQuadraticSqrtExtensionOfNotSquare
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsSupUnitsLocalNormsSqrtNeTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRingHomAdicCompletionUnder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsAuxiliaryPlacesSquarePatternsSUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsUnionSupLocalSquaresEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfSUnitLocalSquareFiniteRealPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitMemGlobalNormOfMemLocalNorms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HasseNormTheoremQuadraticExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexUnitsLocalSquaresFiniteRealPlacesLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EvenCardOfNotLone
import Theorems.Thm_GlobalTheory_HilbertRecip_hs_eq_one_iff
import Theorems.Thm_GlobalTheory_HilbertRecip_hs_eq_neg_one_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm GlobalTheory.QuadSymbol.NormIndex
noncomputable section
open GlobalTheory GlobalTheory.HilbertRecip
variable {F : Type} [Field F] [NumberField F]
open Classical
namespace GlobalTheory.HilbertRecip
theorem _root_.solution (L : Finset (Place F)) (c : Place F → Fˣ) (q : Place F) (b : Fˣ)
    (h1 : q ∈ L → c q ∉ nrm q b) (h2 : ∀ p ∈ L, p ≠ q → c p ∈ nrm q b) :
    hs q (∏ p ∈ L, c p) b = if q ∈ L then -1 else 1 := by
  have key : hs q (∏ p ∈ L, c p) b = ∏ p ∈ L, hs q (c p) b := by
    exact map_prod (hsLeft q b) c L
  rw [key]
  split_ifs with hq
  · rw [Finset.prod_eq_single q (fun p hp hpq => hs_eq_one_iff.mpr (h2 p hp hpq))
      (fun h => absurd hq h)]
    exact hs_eq_neg_one_iff.mpr (h1 hq)
  · exact Finset.prod_eq_one (fun p hp => hs_eq_one_iff.mpr (h2 p hp (fun h => hq (h ▸ hp))))
end GlobalTheory.HilbertRecip
