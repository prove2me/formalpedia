-- Prove2me | solution 1 for GlobalTheory.RegSS.Semilocal.krylov_map_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:26.795897+00:00
-- url     : https://prove2.me/submissions/6680486d-f9bf-4db9-97a3-0538508a8803

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CyclicVectorSemilocalOfCyclicVectorField
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open GlobalTheory.RegSS Matrix
open GlobalTheory GlobalTheory.RegSS GlobalTheory.RegSS.Semilocal
open Matrix
namespace GlobalTheory.RegSS.Semilocal
namespace _root_.GlobalTheory.RegSS.Semilocal
theorem _root_.solution {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {n : Type}
    [Fintype n] [DecidableEq n] (M : Matrix n n A) (v : n → A) :
    (_root_.GlobalTheory.RegSS.krylov M v).map f = _root_.GlobalTheory.RegSS.krylov (M.map f) (f ∘ v) := by
  ext i j
  simp only [_root_.GlobalTheory.RegSS.krylov, Matrix.map_apply, Matrix.of_apply, RingHom.map_mulVec]
  congr 2
  exact RingHom.map_pow f.mapMatrix M _
end _root_.GlobalTheory.RegSS.Semilocal
end GlobalTheory.RegSS.Semilocal
