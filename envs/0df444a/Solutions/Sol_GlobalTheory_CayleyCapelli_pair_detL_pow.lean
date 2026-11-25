-- Prove2me | solution 1 for GlobalTheory.CayleyCapelli.pair_detL_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:57:16.131964+00:00
-- url     : https://prove2.me/submissions/2f9b9a8e-4bff-45a9-ab96-cef4187a10f0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdIccMulFactorial
import Theorems.Thm_GlobalTheory_CayleyCapelli_detL_eq
import Theorems.Thm_GlobalTheory_CayleyCapelli_pair_detL
import Theorems.Thm_ReciprocityTheory_PGsh_cayley


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds
noncomputable section
open GlobalTheory GlobalTheory.CayleyCapelli
open MvPolynomial Formalism.IncomingBounds ReciprocityTheory.PGsh GlobalTheory.DetPowPairing
variable {σ : Type} {C : Type} [Field C]
namespace GlobalTheory.CayleyCapelli
theorem _root_.solution (n s : ℕ) (P : MvPolynomial (PVar n) C) :
    pair (P * detL C n) (detL C n ^ (s + 1)) =
      ((∏ c ∈ Finset.range n, (s + 1 + c) : ℕ) : C) * pair P (detL C n ^ s) := by
  have e : detL C n ^ (s + 1) = rename Sum.inl (cayDet n C ^ (s + 1)) := by rw [detL_eq, map_pow]
  rw [e, pair_detL, cayley n C (s + 1), Nat.add_sub_cancel, map_nsmul, map_nsmul,
    nsmul_eq_mul, map_pow, ← detL_eq]
end GlobalTheory.CayleyCapelli
