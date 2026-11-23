-- Prove2me | solution 1 for GlobalTheory.PMonE.LangOnto.backPoly_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:39:11.195413+00:00
-- url     : https://prove2.me/submissions/499aff2e-7793-47ad-818f-b1f6a3c95f0b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_GroundTheory_PAdicHodge_SemilinearResidue
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralSolutionFrobeniusSubMulVecEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE GlobalTheory.PMonE.LangOnto
open Polynomial Finset GlobalTheory.PMonE
namespace GlobalTheory.PMonE.LangOnto
theorem _root_.solution {k : Type*} [Field k] (q n : ℕ) (c : ℕ → k) : backPoly q n c 0 = X := rfl
end GlobalTheory.PMonE.LangOnto
