-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.NormBaseChange.indexTwo_infinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:42:44.313935+00:00
-- url     : https://prove2.me/submissions/53f341ff-ded3-432d-885d-15eccbad7e2a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSquareMulInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticExtNormFormOverAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsKum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CyclicKummerNormFixedHilbert90
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HerbrandPrimeOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PIdxUnitsFiniteExtensionAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSubgroupIndexTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndexTwoOfFiniteReal
import Theorems.Thm_GlobalTheory_QuadSymbol_NormBaseChange_IndexTwo_of_ringEquiv
import Theorems.Thm_GlobalTheory_QuadSymbol_NormBaseChange_indexTwo_of_isAlgClosed
import Theorems.Thm_GlobalTheory_QuadSymbol_NormBaseChange_indexTwo_of_finite_real
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_Nm_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped WithZero
open GlobalTheory GlobalTheory.QuadSymbol
open GlobalTheory.QuadSymbol.NormBaseChange
open NormIndex
namespace GlobalTheory.QuadSymbol.NormBaseChange
theorem _root_.solution (F : Type) [Field F] (w : InfinitePlace F) (B : Type) [Field B]
    [Algebra w.Completion B] [FiniteDimensional w.Completion B] : IndexTwo B := by
  rcases w.isReal_or_isComplex with hw | hw
  · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
    letI : Algebra ℝ w.Completion := (e.symm : ℝ →+* w.Completion).toAlgebra
    letI : Algebra ℝ B := ((algebraMap w.Completion B).comp (e.symm : ℝ →+* w.Completion)).toAlgebra
    haveI : IsScalarTower ℝ w.Completion B := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : Algebra.IsAlgebraic ℝ w.Completion := ⟨fun x => by
      have : x = algebraMap ℝ w.Completion (e x) := (e.symm_apply_apply x).symm
      rw [this]
      exact isAlgebraic_algebraMap _⟩
    haveI : Algebra.IsAlgebraic ℝ B := Algebra.IsAlgebraic.trans ℝ w.Completion B
    exact indexTwo_of_finite_real B
  · let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
    haveI : IsAlgClosed w.Completion := IsAlgClosed.of_ringEquiv ℂ _ e.symm
    haveI : IsAlgClosed B := IsAlgClosed.of_ringEquiv w.Completion _
      (RingEquiv.ofBijective (algebraMap w.Completion B)
        (IsAlgClosed.algebraMap_bijective_of_isIntegral))
    exact indexTwo_of_isAlgClosed B
end GlobalTheory.QuadSymbol.NormBaseChange
