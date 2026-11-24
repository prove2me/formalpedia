-- Prove2me | solution 1 for GlobalTheory.torusEval_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:37:37.009922+00:00
-- url     : https://prove2.me/submissions/1473036b-5083-456a-9bee-8e22b5895911

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology
open GlobalTheory
open AddMonoidAlgebra
variable {R : Type*} [CommRing R] {X : Type*} [AddCommGroup X]
namespace GlobalTheory
theorem _root_.solution :
    Function.Bijective (torusEval : (Multiplicative X →* Rˣ) → (AddMonoidAlgebra R X →ₐ[R] R)) := by
  constructor
  · intro s t h
    refine MonoidHom.ext fun x => Units.ext ?_
    simpa using congrArg (fun φ : AddMonoidAlgebra R X →ₐ[R] R => φ (single x.toAdd 1)) h
  · intro φ
    refine ⟨((AddMonoidAlgebra.lift R R X).symm φ).toHomUnits, ?_⟩
    rw [torusEval]
    conv_rhs => rw [← (AddMonoidAlgebra.lift R R X).apply_symm_apply φ]
    congr 1
end GlobalTheory
