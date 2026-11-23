-- Prove2me | solution 1 for GlobalTheory.Serre.mulChar_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:10.490533+00:00
-- url     : https://prove2.me/submissions/9f9f1b8d-0c4a-475e-87e1-035ea7e87d9d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedRingOfIntegers

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
open TensorProduct
open GlobalTheory GlobalTheory.Serre
variable {R O O' : Type*} [CommRing R] [CommRing O] [CommRing O'] [Algebra O O'] [Algebra O R]
  [Algebra O' R] [IsScalarTower O O' R]
namespace GlobalTheory.Serre
theorem _root_.solution (r : R) (x : O') :
    mulChar R O O' (r ⊗ₜ x) = r * algebraMap O' R x := rfl
end GlobalTheory.Serre
