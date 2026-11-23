-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.baseChange_eq_span_image
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:18.324769+00:00
-- url     : https://prove2.me/submissions/1d078ba7-82c1-4faa-8d43-42170befec79

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
theorem _root_.solution (N : Submodule K V) :
    N.baseChange L = Submodule.span L (TensorProduct.mk K L V 1 '' N) :=
  Submodule.baseChange_eq_span L N
end GlobalTheory.GaloisDescent
