-- Prove2me | solution 1 for GlobalTheory.T.unitLemma_local_oddResidue_of_lieAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:25:49.11314+00:00
-- url     : https://prove2.me/submissions/b1db1792-2045-4b7b-b960-568216f9dfae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaLocalOddResidueOfLieAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaLocalOddResidueOfLieAlgebraStatement
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_unitLemma_local_of_lie


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : UnitLemmaLie → ∀ (K : UQ), K.Odd → ∀ B₁ B₂ : InvAlg K, B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → IsLocalRing (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) → InvAlg.Identity B₁ B₂ := by
  first | exact @GlobalTheory.UnitLemma.Unr.unitLemma_local_of_lie | exact GlobalTheory.UnitLemma.Unr.unitLemma_local_of_lie | (intros; apply GlobalTheory.UnitLemma.Unr.unitLemma_local_of_lie <;> assumption)
end _root_.GlobalTheory.T
