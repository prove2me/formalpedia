-- Prove2me | solution 1 for GlobalTheory.cochain_comm_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:57.935192+00:00
-- url     : https://prove2.me/submissions/3fa1694c-62e4-489c-894f-a71d7d7dd77a

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
theorem _root_.solution {K C : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ C) (i j : ℕ)
    (x : K.X i) : (C.d i j).hom ((φ.f i).hom x) = (φ.f j).hom ((K.d i j).hom x) :=
  congr($(φ.comm i j).hom x)
end GlobalTheory
