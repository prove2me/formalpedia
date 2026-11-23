-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.mem_rationalPart
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:57:49.91361+00:00
-- url     : https://prove2.me/submissions/9702ee50-fd96-44b0-9356-a9d645ebf969

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open GlobalTheory GlobalTheory.GaloisDescent
variable {K L V G : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V]
namespace GlobalTheory.GaloisDescent
theorem _root_.solution {W : Submodule L (L ⊗[K] V)} {v : V} :
    v ∈ rationalPart K W ↔ (1 : L) ⊗ₜ[K] v ∈ W := Iff.rfl
end GlobalTheory.GaloisDescent
