-- Prove2me | solution 1 for GlobalTheory.PointFunction.nonempty_algHom_algebraicClosure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:05:53.111816+00:00
-- url     : https://prove2.me/submissions/4428de24-ad6e-4372-8572-17c1e890248d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NonemptyAlgHomAlgebraicClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PointFunction
open IsLocalRing
namespace GlobalTheory.PointFunction
theorem _root_.solution (F k : Type) [Field F] [Field k] [IsAlgClosed k]
    [Algebra F k] : Nonempty (AlgebraicClosure F →ₐ[F] k) :=
  ⟨IsAlgClosed.lift⟩
end GlobalTheory.PointFunction
