-- Prove2me | solution 1 for GlobalTheory.CayleyCapelli.detL_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:39:50.105029+00:00
-- url     : https://prove2.me/submissions/19c0ef10-5055-4bf1-a8a5-293dcb43a564

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdIccMulFactorial

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
theorem _root_.solution (n : ℕ) : detL C n = rename Sum.inl (cayDet n C) := by
  rw [detL, cayDet, AlgHom.map_det]
  congr 1
  ext b c
  simp [Matrix.mvPolynomialX]
end GlobalTheory.CayleyCapelli
