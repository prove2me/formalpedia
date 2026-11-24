-- Prove2me | solution 1 for GlobalTheory.unit_pmul_zmod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:39:41.311811+00:00
-- url     : https://prove2.me/submissions/75989b2a-387b-4b87-9f77-d6a866647d7f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShortExactMulPrimeZmodTensorComplex
import Theorems.Thm_GlobalTheory_oneZ_tmul_p

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
theorem _root_.solution (p : ℕ) (M : ModuleCat.{0} ℤ) (x : M) :
    ((ModuleCat.extendRestrictScalarsAdj (Int.castRingHom (ZMod p))).unit.app M).hom
      (((p : ℤ) • LinearMap.id : M →ₗ[ℤ] M) x) = 0 :=
  (ModuleCat.extendRestrictScalarsAdj_unit_app_apply _ _ _).trans (oneZ_tmul_p p M x)
end GlobalTheory
