-- Prove2me | solution 1 for GlobalTheory.Cyc.FontW.Cpl.tensor_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:39:26.109905+00:00
-- url     : https://prove2.me/submissions/9a5757b8-6e59-42bf-b073-69261e507b01

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRight
import Theorems.Thm_GlobalTheory_Cyc_FontW_Cpl_equiv
import Theorems.Thm_GlobalTheory_Cyc_FontW_Cpl_tensor_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.FontW
namespace GlobalTheory.Cyc.FontW
namespace Cpl
theorem _root_.solution {l : ℕ} {R P M : Type*} [CommRing R] [AddCommGroup P] [Module R P]
    [Module.Free R P] [Module.Finite R P] [AddCommGroup M] [Module R M] (h : Cpl l M) :
    Cpl l (TensorProduct R M P) :=
  Cpl.equiv (TensorProduct.comm R M P).toAddEquiv h.tensor_left
end Cpl
end GlobalTheory.Cyc.FontW
