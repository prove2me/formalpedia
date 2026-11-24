-- Prove2me | solution 1 for GlobalTheory.unit_surjective_zmod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:39:41.939251+00:00
-- url     : https://prove2.me/submissions/e8e39598-05ac-4d03-baec-4cc77efb5a43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShortExactMulPrimeZmodTensorComplex
import Theorems.Thm_GlobalTheory_oneZ_tmul_surjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (p : ℕ) (M : ModuleCat.{0} ℤ) :
    Function.Surjective ((ModuleCat.extendRestrictScalarsAdj (Int.castRingHom (ZMod p))).unit.app M).hom := by
  intro t
  obtain ⟨m, hm⟩ := oneZ_tmul_surjective p M t
  exact ⟨m, (ModuleCat.extendRestrictScalarsAdj_unit_app_apply _ _ _).trans hm⟩
end GlobalTheory
