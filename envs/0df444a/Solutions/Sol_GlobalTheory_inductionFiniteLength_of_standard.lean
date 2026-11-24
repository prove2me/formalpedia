-- Prove2me | solution 1 for GlobalTheory.inductionFiniteLength_of_standard
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:00:10.940009+00:00
-- url     : https://prove2.me/submissions/26c8835d-e5ea-4424-8c7c-a8f090569808

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IrreducibleAdmissibleGL_69e19a0de021488a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__StandardFunctorsFiniteLength_93eb2991d501e04b
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeviBlocksParabolicInductionFiniteLength
import Theorems.Thm_GlobalTheory_BlockReorder_blockSize_pos
import Theorems.Thm_GlobalTheory_BlockReorder_leviMap_surjective
import Theorems.Thm_GlobalTheory_BlockReorder_continuous_leviMap
import Theorems.Thm_GlobalTheory_BlockReorder_hasFiniteLength_parInd
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_hasFiniteLength_comp_iff
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL Matrix
open GlobalTheory
open BlockReorder
namespace GlobalTheory
theorem _root_.solution : GlobalTheory.Published.StandardFunctorsFiniteLength →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      GlobalTheory.SmGL.InductionFiniteLength k := by
  intro hP k _ _ _ _ α n m _ _ _ _ _ _ e W _ _ ρ hρ hl
  refine hasFiniteLength_parInd e ρ ((hP k (numBlocks m) (blockSize m) blockSize_pos).2 W (ρ.comp (leviMap k e))
    (isSmooth_comp hρ _ (continuous_leviMap e)) ((hasFiniteLength_comp_iff _ _ (leviMap_surjective e)).2 hl))
end GlobalTheory
