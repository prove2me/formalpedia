-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.isPre_of_separable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:40:11.958602+00:00
-- url     : https://prove2.me/submissions/7f0bfdca-8fb9-4e5b-87b0-e85f8c1e9b7c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsReducedOfSeparableMarkedCharpoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvolutionIdempotentDecompositionOfSeparableChar
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_exists_isPre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
open Classical
namespace GlobalTheory.UnitLemma.Desc
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K), B.P.Separable →
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → B.A) (S : Finset ι), IsPre B e S := fun K B hP => exists_isPre K B hP
end GlobalTheory.UnitLemma.Desc
