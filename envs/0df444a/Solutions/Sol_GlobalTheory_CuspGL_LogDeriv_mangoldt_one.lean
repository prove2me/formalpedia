-- Prove2me | solution 1 for GlobalTheory.CuspGL.LogDeriv.mangoldt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:02:52.230799+00:00
-- url     : https://prove2.me/submissions/475628ca-1313-4d63-b125-d73207daa0ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MonicFactorizationConvolutionFiniteCommAssocAddStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_AdditiveEqPolynomialVonMangoldtConvolutionOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_AdditiveMulEqVonMangoldtConvolution

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
noncomputable section
open GlobalTheory GlobalTheory.CuspGL GlobalTheory.CuspGL.LogDeriv
variable {F : Type} [Field F]
namespace GlobalTheory.CuspGL.LogDeriv
theorem _root_.solution (s : F[X] → ℂ) : mangoldt s 1 = 0 := by
  unfold mangoldt
  refine finsum_mem_eq_zero_of_forall_eq_zero ?_
  rintro f ⟨_, hf, m, hm, h⟩
  exact absurd (IsUnit.of_pow_eq_one h.symm hm.ne') hf.not_isUnit
end GlobalTheory.CuspGL.LogDeriv
