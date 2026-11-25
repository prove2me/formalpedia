-- Prove2me | solution 1 for GlobalTheory.T.involutionIdempotentDecomposition_of_separable_charpoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:21:56.549603+00:00
-- url     : https://prove2.me/submissions/877c8131-76e9-4d17-8169-dee6d1759fd1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvolutionIdempotentDecompositionOfSeparableChar
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvolutionIdempotentDecompositionOfSeparableCharStatement
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_isPre_of_separable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∃ (ι : Type) (_ : Fintype ι) (e : ι → B.A) (S : Finset ι), IsPre B e S := by
  first | exact @GlobalTheory.UnitLemma.Desc.isPre_of_separable | exact GlobalTheory.UnitLemma.Desc.isPre_of_separable | (intros; apply GlobalTheory.UnitLemma.Desc.isPre_of_separable <;> assumption)
end _root_.GlobalTheory.T
