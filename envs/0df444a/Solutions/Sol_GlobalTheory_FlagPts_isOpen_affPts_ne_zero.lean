-- Prove2me | solution 1 for GlobalTheory.FlagPts.isOpen_affPts_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:41:45.817095+00:00
-- url     : https://prove2.me/submissions/71c6a7de-7ad1-446e-b481-597da9edf220

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UniMatBlockTriangular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Module TopologicalSpace
open GlobalTheory GlobalTheory.FlagPts
namespace GlobalTheory.FlagPts
theorem _root_.solution {k J : Type} [Field k] (p : MvPolynomial J k) :
    IsOpen {x : AffPts k J | MvPolynomial.eval x p ≠ 0} :=
  isOpen_generateFrom_of_mem ⟨p, rfl⟩
end GlobalTheory.FlagPts
