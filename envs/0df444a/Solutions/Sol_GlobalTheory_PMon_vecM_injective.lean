-- Prove2me | solution 1 for GlobalTheory.PMon.vecM_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:17:32.334879+00:00
-- url     : https://prove2.me/submissions/5237e3c8-feb4-4a1a-8f58-23016bfe4bc5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KroneckerTransposeMulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.PMon
variable {R : Type*} [CommRing R] {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
namespace GlobalTheory.PMon
theorem _root_.solution {S : Type*} : Function.Injective (vecM : Matrix a b S → a × b → S) := by
  intro X Y h
  ext i j
  exact congrFun h (i, j)
end GlobalTheory.PMon
