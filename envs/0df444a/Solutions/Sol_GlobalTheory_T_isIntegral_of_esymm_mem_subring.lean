-- Prove2me | solution 1 for GlobalTheory.T.isIntegral_of_esymm_mem_subring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:16:08.27054+00:00
-- url     : https://prove2.me/submissions/2ba86b30-829d-471d-bed4-57d5bb5edd3c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralOfEsymmMemSubring
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralOfEsymmMemSubringStatement
import Theorems.Thm_GlobalTheory_QFam_isIntegral_of_esymm_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] (R : Subring ℂ) (x : ι → ℂ), (∀ k : ℕ, (∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, x i) ∈ R) → ∀ i, IsIntegral R (x i) := by
  first | exact @GlobalTheory.QFam.isIntegral_of_esymm_mem | exact GlobalTheory.QFam.isIntegral_of_esymm_mem | (intros; apply GlobalTheory.QFam.isIntegral_of_esymm_mem <;> assumption)
end _root_.GlobalTheory.T
