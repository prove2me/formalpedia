-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.FlagTrdeg.isTranscendenceBasis_of_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:18:38.289999+00:00
-- url     : https://prove2.me/submissions/21191367-a681-4a35-8fcc-f5178e60fa6b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsGenericFlag
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_GenericFlagTrdegFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.Ar
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagTrdeg
open scoped IntermediateField.algebraAdjoinAdjoin
namespace GlobalTheory.CompanionTheory.Ar.FlagTrdeg
theorem _root_.solution {k K ι : Type} [Field k] [Field K] [Algebra k K] {x : ι → K}
    (hx : AlgebraicIndependent k x)
    (h : Algebra.IsAlgebraic (IntermediateField.adjoin k (Set.range x)) K) :
    IsTranscendenceBasis k x := by
  rw [hx.isTranscendenceBasis_iff_isAlgebraic]
  exact (IsFractionRing.comap_isAlgebraic_iff (A := ↥(Algebra.adjoin k (Set.range x)))
    (K := ↥(IntermediateField.adjoin k (Set.range x))) (C := K)).2 h
end GlobalTheory.CompanionTheory.Ar.FlagTrdeg
