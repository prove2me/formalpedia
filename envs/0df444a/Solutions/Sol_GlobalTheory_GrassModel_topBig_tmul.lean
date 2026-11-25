-- Prove2me | solution 1 for GlobalTheory.GrassModel.topBig_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:49:32.854563+00:00
-- url     : https://prove2.me/submissions/46ca7836-e589-4dfc-b7b4-c4edd9dc51c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_VecMulVecComm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial TensorProduct
open GlobalTheory GlobalTheory.GrassModel
variable (n : ℕ)
namespace GlobalTheory.GrassModel
theorem _root_.solution (x y : Ext n) : topBig n (x ⊗ₜ y) = topExt n x * topExt n y := rfl
end GlobalTheory.GrassModel
