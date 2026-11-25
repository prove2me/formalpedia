-- Prove2me | solution 1 for GlobalTheory.Nef.OrdCalc.nrm_unimod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:21:32.149816+00:00
-- url     : https://prove2.me/submissions/8cf9ad53-7728-4a17-873d-fadc472bd1ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceOrderCalculus
import Theorems.Thm_GlobalTheory_Nef_OrdCalc_nrm_mulVec_le
import Theorems.Thm_GlobalTheory_Nef_OrdCalc_unimod_mul_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option autoImplicit false
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.OrdCalc
variable {k F : Type} [Field k] [Field F] [Algebra k F]
namespace GlobalTheory.Nef.OrdCalc
theorem _root_.solution (v : Place k F) (n : ℕ) (u : Matrix (Fin n) (Fin n) F) (x : Fin n → F)
    (hu : Unimod v u) : nrm v (u.mulVec x) = nrm v x := by
  have hd : IsUnit u.det := isUnit_iff_ne_zero.2 (fun h => by
    have := hu.2; rw [h, map_zero] at this; exact zero_ne_one this)
  apply le_antisymm (nrm_mulVec_le v n u x hu.1)
  have h := nrm_mulVec_le v n u⁻¹ (u.mulVec x) (unimod_mul_inv v n u u hu hu).2.1
  rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul u hd, Matrix.one_mulVec] at h
end GlobalTheory.Nef.OrdCalc
