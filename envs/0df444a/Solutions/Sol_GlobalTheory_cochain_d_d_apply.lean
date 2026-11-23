-- Prove2me | solution 1 for GlobalTheory.cochain_d_d_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:24.099517+00:00
-- url     : https://prove2.me/submissions/d78b5d76-bfdf-4bdc-83a1-71b8ba1a5f0c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory TensorProduct
universe u v w
open GlobalTheory
variable {R : Type u} [Ring R]
namespace GlobalTheory
theorem _root_.solution (K : CochainComplex (ModuleCat.{v} R) ℕ) (i j k : ℕ) (x : K.X i) :
    (K.d j k).hom ((K.d i j).hom x) = 0 := congr($(K.d_comp_d i j k).hom x)
end GlobalTheory
