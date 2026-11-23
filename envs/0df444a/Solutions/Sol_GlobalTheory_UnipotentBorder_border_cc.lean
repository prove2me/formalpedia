-- Prove2me | solution 1 for GlobalTheory.UnipotentBorder.border_cc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:34:16.440016+00:00
-- url     : https://prove2.me/submissions/cc75b430-d7c4-4abb-a2a8-3e509fbafffe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IwahoriFactorisation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnipotentBorder
open Matrix
variable {O : Type} [CommRing O]
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) O) (col row : Fin n → O) (x : O)
omit [CommRing O]
namespace GlobalTheory.UnipotentBorder
theorem _root_.solution (i j : Fin n) : border A col row x i.castSucc j.castSucc = A i j := by simp [border]
end GlobalTheory.UnipotentBorder
