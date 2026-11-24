-- Prove2me | solution 1 for GlobalTheory.HilbertRecip.exists_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:19:40.863663+00:00
-- url     : https://prove2.me/submissions/a7b408ed-29fc-4143-a85d-3ec1375eb685

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
import Theorems.Thm_GlobalTheory_QNorm_exists_approx_mod_squares
import Theorems.Thm_GlobalTheory_QNorm_mem_sqSub
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_Nm_symm


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
namespace GlobalTheory.HilbertRecip
theorem _root_.solution (S : Finset (HeightOneSpectrum (𝓞 F))) (y : Place F → Fˣ) :
    ∃ x : Fˣ, ∀ p, Over S p → x * y p ∈ sqr p := by
  obtain ⟨x, hx0, hS, hR⟩ := exists_approx_mod_squares F S
    (fun v => algebraMap F (v.adicCompletion F) (y (.inl v) : F)) (fun σ => σ (y (.inr σ) : F))
    (fun v => (map_ne_zero _).2 (y _).ne_zero) (fun σ => (map_ne_zero _).2 (y _).ne_zero)
  refine ⟨Units.mk0 x hx0, fun p hp => ?_⟩
  cases p with
  | inl v =>
    show _ ∈ sqSub _
    rw [mem_sqSub, Units.val_mul, Units.val_mk0, map_mul]
    exact hS v hp
  | inr σ =>
    show _ ∈ sqSub _
    rw [mem_sqSub, Units.val_mul, Units.val_mk0, map_mul]
    have h := hR σ
    exact ⟨Real.sqrt _, (Real.mul_self_sqrt h.le).symm⟩
end GlobalTheory.HilbertRecip
